/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.CliffordSplitEnvelope
import InfoGeometry.Physics.Cl55FiveGradeDualityBridge
import InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
import InfoGeometry.Synthesis.HestenesStokesAlgebraicBoundarySynthesis

/-!
# $\mathrm{Cl}(5,5)$ Five-Graded Duality, Para-Kähler Split Envelope, and Permutation-Equivariant Fisher–Souriau Attention Unification

This module unifies the neutral para-Kähler split quadratic envelope of $\mathrm{Cl}(N,N)$, the
five-graded Kantor–Koecher–Tits grade-reversal intertwining across colimit cone homomorphisms,
and the symmetric-group permutation equivariance of the Souriau–Massieu free entropy potential
and Fisher–Souriau attention Laplacian:

1. **Para-Kähler $\mathrm{Cl}(N,N)$ Split Quadratic Envelope & Non-Degenerate Vacuum Pairing (`Section 1`)**:
   - Proves `paraKahler_sum_quadratic_eq_two_pairing` and
     `paraKahler_split_envelope_and_isotropic_vacuum_duality`:
     for any real module $V$, linear involution $K : V \to_{\mathbb{R}} V$ ($K^2 = \mathrm{id}$),
     and symmetric $K$-anti-invariant bilinear form $g$ ($g(Ku, Kv) = -g(u, v)$), every vector's
     quadratic form splits into twice the cross-sheet pairing $2 g(P^+ v, P^- v)$, both eigen-sheets
     `primalSheet K` and `covectorVacuumSheet K` are totally $g$-isotropic, the quadratic form on
     $u + \alpha$ ($u \in V^+, \alpha \in V^-$) equals $2 g(u, \alpha)$, and non-degeneracy of $g$
     forces any primal vector orthogonal to `covectorVacuumSheet K` to vanish.

2. **Five-Graded Grade Reversal Intertwining Across Colimit Cone Homomorphisms (`Section 2`)**:
   - Defines `IsConformalFiveGradePreserving` and `IsGradeReversalIntertwined` over
     `SuperTKKConformalClosure.FiveGrading` and `Cl55FiveGradeDualityBridge.GradeReversal`.
   - Proves `gradeReversal_colimit_full_channel_intertwining`: given a colimit cone triangle
     $\iota_m \circ b_{nm} = \iota_n$ whose morphisms preserve the five homogeneous grades and
     intertwine the grade reversals $(R_n, R_m, R_\infty)$, the cone injection $\iota_n$ preserves
     all five grades, intertwines $R_n$ with $R_\infty$, and transports all three grade-reversed
     bracket channels $(+1, +1) \to -2$, $(-1, -1) \to +2$, and $(-1, +1) \to 0$ into the colimit
     five-grading $G_\infty$.

3. **Permutation Equivariance of the Souriau–Massieu Potential & Fisher–Souriau Laplacian (`Section 3`)**:
   - Proves `souriauPartition_perm_invariant`, `souriauMassieuPotential_perm_invariant`,
     `gibbsProb_perm_equivariant`, and `fisherSouriauLaplacian_perm_equivariant` under the
     symmetric group $\mathrm{Perm}(\mathrm{Fin}\, n)$.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification

noncomputable section

open scoped BigOperators Matrix
open Finset Matrix Real
open InfoGeometry.SuperGrassmannian
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Physics.Cl55FiveGradeDualityBridge
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
open InfoGeometry.Synthesis.HestenesStokesAlgebraicBoundarySynthesis

/-!
## Section 1: Para-Kähler $\mathrm{Cl}(N,N)$ Split Quadratic Envelope & Non-Degenerate Vacuum Pairing
-/

/-- For any primal vector $u \in \mathrm{primalSheet}(K)$ and covector vacuum element
$\alpha \in \mathrm{covectorVacuumSheet}(K)$, total isotropy of the two para-Kähler eigen-sheets
and symmetry of $g$ reduce the quadratic form on $u + \alpha$ to twice their cross-sheet pairing:
$$g(u + \alpha, u + \alpha) = 2 g(u, \alpha).$$ -/
lemma paraKahler_sum_quadratic_eq_two_pairing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : V →ₗ[ℝ] V) (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hK : ∀ v, K (K v) = v)
    (h_symm : ∀ u v, g u v = g v u)
    (hg : ∀ u v, g (K u) (K v) = - g u v)
    {u α : V} (hu : u ∈ primalSheet K) (hα : α ∈ covectorVacuumSheet K) :
    g (u + α) (u + α) = 2 * g u α := by
  have huu : g u u = 0 := primal_sheet_is_isotropic K hK g hg u u hu hu
  have hαα : g α α = 0 := covector_vacuum_sheet_is_isotropic K hK g hg α α hα hα
  have h_expand : g (u + α) (u + α) = g u u + g u α + g α u + g α α := by
    simp only [map_add, LinearMap.add_apply]
    abel
  have h_cross : g α u = g u α := h_symm α u
  rw [huu, hαα, h_cross] at h_expand
  linarith

/-- Para-Kähler $\mathrm{Cl}(N,N)$ Split Quadratic Envelope and Isotropic Vacuum Duality:
1. Every vector's quadratic form splits into twice the cross-sheet pairing between its primal and
   covector vacuum projections:
   $g(v, v) = 2 g(P^+ v, P^- v)$.
2. Both `primalSheet K` and `covectorVacuumSheet K` are totally isotropic with respect to $g$.
3. For any $u \in \mathrm{primalSheet}(K)$ and $\alpha \in \mathrm{covectorVacuumSheet}(K)$,
   $g(u + \alpha, u + \alpha) = 2 g(u, \alpha)$.
4. When $g$ is non-degenerate on $V$, any primal vector $u \in \mathrm{primalSheet}(K)$ orthogonal
   to `covectorVacuumSheet K` vanishes ($u = 0$). -/
theorem paraKahler_split_envelope_and_isotropic_vacuum_duality
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : V →ₗ[ℝ] V) (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hK : ∀ v, K (K v) = v)
    (h_symm : ∀ u v, g u v = g v u)
    (hg : ∀ u v, g (K u) (K v) = - g u v)
    (hg_nondeg : ∀ u, (∀ w, g u w = 0) → u = 0) :
    (∀ v : V, g v v = 2 * g (paraProjectorPlus K v) (paraProjectorMinus K v)) ∧
    ((∀ u₁ ∈ primalSheet K, ∀ u₂ ∈ primalSheet K, g u₁ u₂ = 0) ∧
     (∀ α₁ ∈ covectorVacuumSheet K, ∀ α₂ ∈ covectorVacuumSheet K, g α₁ α₂ = 0)) ∧
    (∀ u ∈ primalSheet K, ∀ α ∈ covectorVacuumSheet K, g (u + α) (u + α) = 2 * g u α) ∧
    (∀ u ∈ primalSheet K, (∀ α ∈ covectorVacuumSheet K, g u α = 0) → u = 0) := by
  refine ⟨fun v => cl_nn_quadratic_form_split K g hK h_symm hg v,
          ⟨fun u₁ hu₁ u₂ hu₂ => primal_sheet_is_isotropic K hK g hg u₁ u₂ hu₁ hu₂,
           fun α₁ hα₁ α₂ hα₂ => covector_vacuum_sheet_is_isotropic K hK g hg α₁ α₂ hα₁ hα₂⟩,
          fun u hu α hα => paraKahler_sum_quadratic_eq_two_pairing K g hK h_symm hg hu hα,
          fun u hu h_orth => primal_vacuum_pairing_nondegenerate K g hK hg hg_nondeg u hu h_orth⟩

/-!
## Section 2: Five-Graded Grade Reversal Intertwining Across Colimit Cone Homomorphisms
-/

/-- Predicate asserting that a Lie algebra homomorphism `f : Ln →ₗ⁅ℝ⁆ Lm` preserves all five
homogeneous sectors of a `SuperTKKConformalClosure.FiveGrading`. -/
def IsConformalFiveGradePreserving
    {Ln Lm : Type*}
    [AddCommGroup Ln] [Module ℝ Ln] [LieRing Ln] [LieAlgebra ℝ Ln]
    [AddCommGroup Lm] [Module ℝ Lm] [LieRing Lm] [LieAlgebra ℝ Lm]
    (Gn : SuperTKKConformalClosure.FiveGrading Ln)
    (Gm : SuperTKKConformalClosure.FiveGrading Lm)
    (f : Ln →ₗ⁅ℝ⁆ Lm) : Prop :=
  (∀ x ∈ Gn.gNegTwo, f x ∈ Gm.gNegTwo) ∧
  (∀ x ∈ Gn.gNegOne, f x ∈ Gm.gNegOne) ∧
  (∀ x ∈ Gn.gZero, f x ∈ Gm.gZero) ∧
  (∀ x ∈ Gn.gPosOne, f x ∈ Gm.gPosOne) ∧
  (∀ x ∈ Gn.gPosTwo, f x ∈ Gm.gPosTwo)

/-- Predicate asserting that a Lie algebra homomorphism `f : Ln →ₗ⁅ℝ⁆ Lm` intertwines the
five-grade reversal involutions `Rn : GradeReversal Gn` and `Rm : GradeReversal Gm`. -/
def IsGradeReversalIntertwined
    {Ln Lm : Type*}
    [AddCommGroup Ln] [Module ℝ Ln] [LieRing Ln] [LieAlgebra ℝ Ln]
    [AddCommGroup Lm] [Module ℝ Lm] [LieRing Lm] [LieAlgebra ℝ Lm]
    {Gn : SuperTKKConformalClosure.FiveGrading Ln}
    {Gm : SuperTKKConformalClosure.FiveGrading Lm}
    (Rn : GradeReversal Gn) (Rm : GradeReversal Gm) (f : Ln →ₗ⁅ℝ⁆ Lm) : Prop :=
  ∀ x : Ln, f (Rn.theta x) = Rm.theta (f x)

/-- Composition of conformal five-grade-preserving Lie homomorphisms preserves all five grades. -/
lemma conformalFiveGradePreserving_comp
    {Ln Lm Linf : Type*}
    [AddCommGroup Ln] [Module ℝ Ln] [LieRing Ln] [LieAlgebra ℝ Ln]
    [AddCommGroup Lm] [Module ℝ Lm] [LieRing Lm] [LieAlgebra ℝ Lm]
    [AddCommGroup Linf] [Module ℝ Linf] [LieRing Linf] [LieAlgebra ℝ Linf]
    {Gn : SuperTKKConformalClosure.FiveGrading Ln}
    {Gm : SuperTKKConformalClosure.FiveGrading Lm}
    {Ginf : SuperTKKConformalClosure.FiveGrading Linf}
    {bond_nm : Ln →ₗ⁅ℝ⁆ Lm} {ι_m : Lm →ₗ⁅ℝ⁆ Linf}
    (h_bond : IsConformalFiveGradePreserving Gn Gm bond_nm)
    (h_ιm : IsConformalFiveGradePreserving Gm Ginf ι_m) :
    IsConformalFiveGradePreserving Gn Ginf (ι_m.comp bond_nm) :=
  ⟨fun x hx => h_ιm.1 (bond_nm x) (h_bond.1 x hx),
   fun x hx => h_ιm.2.1 (bond_nm x) (h_bond.2.1 x hx),
   fun x hx => h_ιm.2.2.1 (bond_nm x) (h_bond.2.2.1 x hx),
   fun x hx => h_ιm.2.2.2.1 (bond_nm x) (h_bond.2.2.2.1 x hx),
   fun x hx => h_ιm.2.2.2.2 (bond_nm x) (h_bond.2.2.2.2 x hx)⟩

/-- Along a commutative colimit cone triangle `ι_m.comp bond_nm = ι_n`, grade-reversal intertwining
of `bond_nm` and `ι_m` transfers to `ι_n`. -/
lemma gradeReversalIntertwined_of_cone
    {Ln Lm Linf : Type*}
    [AddCommGroup Ln] [Module ℝ Ln] [LieRing Ln] [LieAlgebra ℝ Ln]
    [AddCommGroup Lm] [Module ℝ Lm] [LieRing Lm] [LieAlgebra ℝ Lm]
    [AddCommGroup Linf] [Module ℝ Linf] [LieRing Linf] [LieAlgebra ℝ Linf]
    {Gn : SuperTKKConformalClosure.FiveGrading Ln}
    {Gm : SuperTKKConformalClosure.FiveGrading Lm}
    {Ginf : SuperTKKConformalClosure.FiveGrading Linf}
    (Rn : GradeReversal Gn) (Rm : GradeReversal Gm) (Rinf : GradeReversal Ginf)
    (bond_nm : Ln →ₗ⁅ℝ⁆ Lm) (ι_n : Ln →ₗ⁅ℝ⁆ Linf) (ι_m : Lm →ₗ⁅ℝ⁆ Linf)
    (h_cone : ι_m.comp bond_nm = ι_n)
    (h_rev_bond : IsGradeReversalIntertwined Rn Rm bond_nm)
    (h_rev_ιm : IsGradeReversalIntertwined Rm Rinf ι_m) :
    IsGradeReversalIntertwined Rn Rinf ι_n := by
  intro x
  have h_app : ∀ z : Ln, ι_m (bond_nm z) = ι_n z := fun z =>
    congrArg (fun φ : Ln →ₗ⁅ℝ⁆ Linf => φ z) h_cone
  rw [← h_app (Rn.theta x), h_rev_bond x, h_rev_ιm (bond_nm x), h_app x]

/-- Five-Graded Colimit Cone Grade-Reversal Full Channel Intertwining:
Given a colimit cone triangle `ι_m.comp bond_nm = ι_n` where `bond_nm` and `ι_m` preserve all five
grades and intertwine the grade reversals `Rn`, `Rm`, `Rinf`, the composite cone injection `ι_n`
intertwines `Rn` and `Rinf`, and for any $x_{-1}, y_{-1} \in G_{n,-1}$ and
$x_{+1}, y_{+1} \in G_{n,+1}$:
1. $\iota_m(b_{nm}(\theta_n \lbrack x_{+1}, y_{+1}\rbrack)) = \theta_\infty \lbrack \iota_n x_{+1}, \iota_n y_{+1}\rbrack \in G_{\infty,-2}$,
2. $\iota_m(b_{nm}(\theta_n \lbrack x_{-1}, y_{-1}\rbrack)) = \theta_\infty \lbrack \iota_n x_{-1}, \iota_n y_{-1}\rbrack \in G_{\infty,+2}$,
3. $\iota_m(b_{nm}(\theta_n \lbrack x_{-1}, y_{+1}\rbrack)) = \theta_\infty \lbrack \iota_n x_{-1}, \iota_n y_{+1}\rbrack \in G_{\infty,0}$. -/
theorem gradeReversal_colimit_full_channel_intertwining
    {Ln Lm Linf : Type*}
    [AddCommGroup Ln] [Module ℝ Ln] [LieRing Ln] [LieAlgebra ℝ Ln]
    [AddCommGroup Lm] [Module ℝ Lm] [LieRing Lm] [LieAlgebra ℝ Lm]
    [AddCommGroup Linf] [Module ℝ Linf] [LieRing Linf] [LieAlgebra ℝ Linf]
    {Gn : SuperTKKConformalClosure.FiveGrading Ln}
    {Gm : SuperTKKConformalClosure.FiveGrading Lm}
    {Ginf : SuperTKKConformalClosure.FiveGrading Linf}
    (Rn : GradeReversal Gn) (Rm : GradeReversal Gm) (Rinf : GradeReversal Ginf)
    (bond_nm : Ln →ₗ⁅ℝ⁆ Lm) (ι_n : Ln →ₗ⁅ℝ⁆ Linf) (ι_m : Lm →ₗ⁅ℝ⁆ Linf)
    (h_cone : ι_m.comp bond_nm = ι_n)
    (h_grade_bond : IsConformalFiveGradePreserving Gn Gm bond_nm)
    (h_grade_ιm : IsConformalFiveGradePreserving Gm Ginf ι_m)
    (h_rev_bond : IsGradeReversalIntertwined Rn Rm bond_nm)
    (h_rev_ιm : IsGradeReversalIntertwined Rm Rinf ι_m)
    {xNeg yNeg xPos yPos : Ln}
    (hxNeg : xNeg ∈ Gn.gNegOne) (hyNeg : yNeg ∈ Gn.gNegOne)
    (hxPos : xPos ∈ Gn.gPosOne) (hyPos : yPos ∈ Gn.gPosOne) :
    IsConformalFiveGradePreserving Gn Ginf ι_n ∧
    IsGradeReversalIntertwined Rn Rinf ι_n ∧
    (ι_m (bond_nm (Rn.theta ⁅xPos, yPos⁆)) = Rinf.theta ⁅ι_n xPos, ι_n yPos⁆ ∧
     Rinf.theta ⁅ι_n xPos, ι_n yPos⁆ ∈ Ginf.gNegTwo) ∧
    (ι_m (bond_nm (Rn.theta ⁅xNeg, yNeg⁆)) = Rinf.theta ⁅ι_n xNeg, ι_n yNeg⁆ ∧
     Rinf.theta ⁅ι_n xNeg, ι_n yNeg⁆ ∈ Ginf.gPosTwo) ∧
    (ι_m (bond_nm (Rn.theta ⁅xNeg, yPos⁆)) = Rinf.theta ⁅ι_n xNeg, ι_n yPos⁆ ∧
     Rinf.theta ⁅ι_n xNeg, ι_n yPos⁆ ∈ Ginf.gZero) := by
  have h_app : ∀ z : Ln, ι_m (bond_nm z) = ι_n z := fun z =>
    congrArg (fun φ : Ln →ₗ⁅ℝ⁆ Linf => φ z) h_cone
  have h_grade_ιn : IsConformalFiveGradePreserving Gn Ginf ι_n := by
    rw [← h_cone]
    exact conformalFiveGradePreserving_comp h_grade_bond h_grade_ιm
  have h_rev_ιn : IsGradeReversalIntertwined Rn Rinf ι_n :=
    gradeReversalIntertwined_of_cone Rn Rm Rinf bond_nm ι_n ι_m h_cone h_rev_bond h_rev_ιm
  have hxNeg_inf : ι_n xNeg ∈ Ginf.gNegOne := h_grade_ιn.2.1 xNeg hxNeg
  have hyNeg_inf : ι_n yNeg ∈ Ginf.gNegOne := h_grade_ιn.2.1 yNeg hyNeg
  have hxPos_inf : ι_n xPos ∈ Ginf.gPosOne := h_grade_ιn.2.2.2.1 xPos hxPos
  have hyPos_inf : ι_n yPos ∈ Ginf.gPosOne := h_grade_ιn.2.2.2.1 yPos hyPos
  refine ⟨h_grade_ιn, h_rev_ιn, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [h_app (Rn.theta ⁅xPos, yPos⁆), h_rev_ιn ⁅xPos, yPos⁆, ι_n.map_lie]
  · exact Rinf.positive_bracket_to_negative hxPos_inf hyPos_inf
  · rw [h_app (Rn.theta ⁅xNeg, yNeg⁆), h_rev_ιn ⁅xNeg, yNeg⁆, ι_n.map_lie]
  · exact Rinf.negative_bracket_to_positive hxNeg_inf hyNeg_inf
  · rw [h_app (Rn.theta ⁅xNeg, yPos⁆), h_rev_ιn ⁅xNeg, yPos⁆, ι_n.map_lie]
  · exact Rinf.mixed_bracket_stays_zero hxNeg_inf hyPos_inf

/-!
## Section 3: Permutation Equivariance of the Souriau–Massieu Potential and Fisher–Souriau Attention Laplacian
-/

/-- Canonical Souriau partition sum $Z(s) = \sum_{i} \exp(s_i)$, aliasing `gibbsPartitionSum`. -/
abbrev souriauPartition {n : ℕ} (s : Fin n → ℝ) : ℝ :=
  gibbsPartitionSum s

/-- Canonical Gibbs probability weight $p_i(s) = \exp(s_i) / Z(s)$, aliasing `souriauAttentionWeight`. -/
abbrev gibbsProb {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  souriauAttentionWeight s i

/-- Canonical Fisher–Souriau attention Laplacian $H_{ij}(s) = p_i(s)\delta_{ij} - p_i(s)p_j(s)$,
aliasing `fisherSouriauHessian`. -/
abbrev fisherSouriauLaplacian {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) : ℝ :=
  fisherSouriauHessian s i j

/-- The Souriau partition sum $Z(s) = \sum_i \exp(s_i)$ is invariant under any permutation
$\sigma \in \mathrm{Perm}(\mathrm{Fin}\, n)$ of the token coordinates. -/
theorem souriauPartition_perm_invariant
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    souriauPartition (s ∘ σ) = souriauPartition s := by
  dsimp [souriauPartition, gibbsPartitionSum, Function.comp]
  exact Equiv.sum_comp σ (fun i => Real.exp (s i))

/-- The Souriau–Massieu free entropy potential $\Phi(s) = \ln Z(s)$ is invariant under any
permutation $\sigma \in \mathrm{Perm}(\mathrm{Fin}\, n)$ of the token coordinates. -/
theorem souriauMassieuPotential_perm_invariant
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    souriauMassieuPotential (s ∘ σ) = souriauMassieuPotential s := by
  unfold souriauMassieuPotential
  have hZ : gibbsPartitionSum (s ∘ σ) = gibbsPartitionSum s :=
    souriauPartition_perm_invariant σ s
  rw [hZ]

/-- The Gibbs probability distribution $p_i(s) = \exp(s_i) / Z(s)$ is equivariant under any
permutation $\sigma \in \mathrm{Perm}(\mathrm{Fin}\, n)$:
$p_i(s \circ \sigma) = p_{\sigma(i)}(s)$. -/
theorem gibbsProb_perm_equivariant
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (i : Fin n) :
    gibbsProb (s ∘ σ) i = gibbsProb s (σ i) := by
  unfold gibbsProb souriauAttentionWeight
  have hZ : gibbsPartitionSum (s ∘ σ) = gibbsPartitionSum s :=
    souriauPartition_perm_invariant σ s
  rw [hZ]
  rfl

/-- The Fisher–Souriau attention Laplacian $H_{ij}(s) = p_i(s)\delta_{ij} - p_i(s)p_j(s)$ is
equivariant under any permutation $\sigma \in \mathrm{Perm}(\mathrm{Fin}\, n)$:
$H_{ij}(s \circ \sigma) = H_{\sigma(i),\sigma(j)}(s)$. -/
theorem fisherSouriauLaplacian_perm_equivariant
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (i j : Fin n) :
    fisherSouriauLaplacian (s ∘ σ) i j = fisherSouriauLaplacian s (σ i) (σ j) := by
  unfold fisherSouriauLaplacian fisherSouriauHessian
  have hi : souriauAttentionWeight (s ∘ σ) i = souriauAttentionWeight s (σ i) :=
    gibbsProb_perm_equivariant σ s i
  have hj : souriauAttentionWeight (s ∘ σ) j = souriauAttentionWeight s (σ j) :=
    gibbsProb_perm_equivariant σ s j
  have h_ite :
      (if i = j then souriauAttentionWeight s (σ i) else 0) =
        (if σ i = σ j then souriauAttentionWeight s (σ i) else 0) := by
    by_cases hij : i = j
    · have hσ : σ i = σ j := σ.injective.eq_iff.mpr hij
      rw [if_pos hij, if_pos hσ]
    · have hσ : σ i ≠ σ j := mt σ.injective.eq_iff.mp hij
      rw [if_neg hij, if_neg hσ]
  rw [hi, hj, h_ite]

end

end InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification
