/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealRotorGaussHestenesBridge
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.HestenesKreinSelfConcordantBarrierColimit
import InfoGeometry.Canonical.KMSInteriorPoint
import InfoGeometry.Canonical.DikinDrazinBridge
import InfoGeometry.Canonical.SL2FiveGradingExample
import InfoGeometry.Categorical.LogJordanResidueCheckedRCalculation
import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis
import InfoGeometry.Synthesis.AmplituhedronBeyondHorizonsGrandSynthesis
import InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis
import InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis
import InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

/-!
# Frontier 111 (Wave 15): Five-Graded Lie Colimit Transport, Drazin–Dikin Barrier Geometry, Hestenes–Stokes Real Boundary Pairing, and Jordan–Souriau Attention Synthesis

This module formalizes the real-geometric boundary and attention calculus in causal order:
1. **Five-Graded Lie Algebra & Graded Colimit Transport (`Section 1`)**:
   - Connects `FiveGrading` (`FiveGradedInformationLedger.lean`), `SL2FiveGradingExample.lean`, and
     `FreudenthalFiveGradedJacobiClosure.lean`.
   - Proves `fiveGradingComap` and `fiveGrading_colimit_cone_bracket_transport` (showing that
     grade-preserving Lie bonding maps $b_{nm} : \mathfrak{g}_n \to \mathfrak{g}_m$ and colimit cone
     maps $\iota_n : \mathfrak{g}_n \to \mathfrak{g}_\infty$ with $\iota_m \circ b_{nm} = \iota_n$
     preserve all five homogeneous grades $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$
     and intertwine all graded Lie brackets).
   - Proves `five_graded_maurer_cartan_equations_and_koszul_supertrace_laws`, establishing all five
     homogeneous components of the Maurer–Cartan flatness equation $d\Omega + \frac{1}{2}[\Omega \wedge \Omega] = 0$
     together with Freudenthal homogeneous Jacobi closure and Koszul coboundary supertrace invariance.
2. **Hestenes–Krein Cone Readouts, Hessian-Compatible Dikin Sets, & Conditional KMS Remainders (`Section 2`)**:
   - Connects `FilteredHestenesKreinColimit.lean`, `HestenesKreinSelfConcordantBarrierColimit.lean`,
     `KMSInteriorPoint.lean`, and `DikinDrazinBridge.lean`.
   - Proves `dikin_hessian_compatible_cone_transport` and
     `drazin_attention_projector_and_colimit_dikin_preservation`: under the stated Hessian equalities,
     the finite-stage Hessian sublevel sets transport along the supplied compatible maps; the
     separate Hestenes–Krein cone readout is compatible. These statements do not construct a
     categorical colimit or prove self-concordant barrier containment. The Drazin result gives
     index-one dynamic/harmonic
     projectors satisfy $P_{\mathrm{dyn}}^2 = P_{\mathrm{dyn}}$, $P_{\mathrm{dyn}} + P_{\mathrm{harm}} = 1$,
     $P_{\mathrm{dyn}} P_{\mathrm{harm}} = 0$, $L P_{\mathrm{harm}} = 0$, and whenever a bonding map
     $\iota_{nm}$ intertwines the Drazin Green operator ($\iota_{nm} L_n^D = L_m^D \iota_{nm}$) and
     preserves the barrier Hessian, it preserves the Drazin–Dikin dynamic attention quadratic form
     $Q_m(\iota_{nm} v) = Q_n(v)$ and maps $\mathcal{E}_n^{\mathrm{dyn}}(x)$ into
     $\mathcal{E}_m^{\mathrm{dyn}}(\iota_{nm} x)$.
3. **Hestenes' 2D Planar Geometric Derivative $\partial = e_1 \partial_x + e_2 \partial_y$ & Monogenicity (`Section 3`)**:
   - Proves `planarClifford_bivector_relations` ($e_1^2 = I_2$, $e_2^2 = I_2$, $e_1 e_2 + e_2 e_1 = 0$,
     $I^2 = -I_2$) and `hestenes_monogenic_factorization_and_cauchy_riemann` ($\partial F = 0$ if and
     only if the Cauchy–Riemann equations hold).
4. **Real Incidence Stokes Pairing & Two-Sheeted Krein Boundary Jumps (`Section 4`)**:
   - Connects `RealRotorGaussHestenesBridge` (`real_boundary_coboundary_pairing`,
     `boundary_zero_of_bulk_zero`), the two-sided jump laws (`boundaryJump_self`,
     `boundaryJump_antisymm`, `boundaryJump_add`), and `krein_two_sheeted_boundary_discontinuity_laws`.
5. **Nilpotent Exponential Truncation, Jordan Monodromy Readout, Shirokov Determinants, & Fisher–Souriau Laplacian Gauge Kernel (`Section 5`)**:
   - Proves `nilpotentExpTrunc_mul_of_sq_zero`, `jordan_shear_composition`, `jordan_double_winding`,
     `jordan_exact_algebraic_readout`, `jordan_hadjiivanov_algebraic_residue_and_shirokov_det_laws`,
     `souriau_massieu_stokes_surprisal_and_chentsov_cumulant_laws`, and
     `fisher_souriau_laplacian_gauge_kernel_and_const_iff` (establishing $H(s)\mathbf{1} = 0$,
     $\ker H(s) = \mathbb{R}\mathbf{1}$, and preservation of normalized attention weights under
     harmonic gauge score shifts).
-/

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open scoped Matrix BigOperators TensorProduct
open Finset Matrix Real
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealIncidenceChains
open InfoGeometry.Canonical.RealIncidenceHomology
open InfoGeometry.Canonical.RealRotorGaussHestenesBridge
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesKreinSelfConcordantBarrierColimit
open InfoGeometry.Canonical.DikinDrazinBridge
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Categorical.LogJordanResidueCheckedRCalculation
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
open InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge
open InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis
open InfoGeometry.Synthesis.AmplituhedronBeyondHorizonsGrandSynthesis
open InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
open InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

namespace InfoGeometry.Synthesis.HestenesStokesAlgebraicBoundarySynthesis

/-!
## Section 1: Five-Graded Lie Algebra Carrier, Grade-Preserving Colimit Bonding Maps, & Five-Graded Maurer–Cartan Decomposition
-/

/-- Predicate asserting that a Lie algebra homomorphism `f : L →ₗ⁅ℝ⁆ L'` between five-graded Lie
algebras `(L, G)` and `(L', G')` maps each of the five homogeneous grade submodules
$\mathfrak{g}_{-2}, \mathfrak{g}_{-1}, \mathfrak{g}_0, \mathfrak{g}_{+1}, \mathfrak{g}_{+2}$
into the corresponding homogeneous grade submodule of `G'`. -/
def IsFiveGradePreservingLieHom
    {L L' : Type*}
    [LieRing L] [LieAlgebra ℝ L]
    [LieRing L'] [LieAlgebra ℝ L']
    (G : FiveGrading L) (G' : FiveGrading L') (f : L →ₗ⁅ℝ⁆ L') : Prop :=
  (∀ x ∈ G.gNegTwo, f x ∈ G'.gNegTwo) ∧
  (∀ x ∈ G.gNegOne, f x ∈ G'.gNegOne) ∧
  (∀ x ∈ G.gZero, f x ∈ G'.gZero) ∧
  (∀ x ∈ G.gPosOne, f x ∈ G'.gPosOne) ∧
  (∀ x ∈ G.gPosTwo, f x ∈ G'.gPosTwo)

/-- Pulling back a `FiveGrading` along any Lie algebra homomorphism `f : L →ₗ⁅ℝ⁆ L'` induces a
canonical `FiveGrading` on `L`. -/
def fiveGradingComap
    {L L' : Type*}
    [LieRing L] [LieAlgebra ℝ L]
    [LieRing L'] [LieAlgebra ℝ L']
    (G' : FiveGrading L') (f : L →ₗ⁅ℝ⁆ L') : FiveGrading L where
  gNegTwo := Submodule.comap f.toLinearMap G'.gNegTwo
  gNegOne := Submodule.comap f.toLinearMap G'.gNegOne
  gZero := Submodule.comap f.toLinearMap G'.gZero
  gPosOne := Submodule.comap f.toLinearMap G'.gPosOne
  gPosTwo := Submodule.comap f.toLinearMap G'.gPosTwo
  negOne_posOne_mem_zero := by
    intro X Y hX hY
    have hX' : f X ∈ G'.gNegOne := by
      rw [Submodule.mem_comap] at hX
      exact hX
    have hY' : f Y ∈ G'.gPosOne := by
      rw [Submodule.mem_comap] at hY
      exact hY
    have h₃ : f ⁅X, Y⁆ ∈ G'.gZero := by
      rw [f.map_lie]
      exact G'.negOne_posOne_mem_zero hX' hY'
    rw [Submodule.mem_comap] at ⊢
    exact h₃
  bracket_negTwo_posTwo := by
    intro X Y hX hY
    have hX' : f X ∈ G'.gNegTwo := by
      rw [Submodule.mem_comap] at hX
      exact hX
    have hY' : f Y ∈ G'.gPosTwo := by
      rw [Submodule.mem_comap] at hY
      exact hY
    have h₃ : f ⁅X, Y⁆ ∈ G'.gZero := by
      rw [f.map_lie]
      exact G'.bracket_negTwo_posTwo (f X) (f Y) hX' hY'
    rw [Submodule.mem_comap] at ⊢
    exact h₃
  posOne_posOne_mem_posTwo := by
    intro X Y hX hY
    have hX' : f X ∈ G'.gPosOne := by
      rw [Submodule.mem_comap] at hX
      exact hX
    have hY' : f Y ∈ G'.gPosOne := by
      rw [Submodule.mem_comap] at hY
      exact hY
    have h₃ : f ⁅X, Y⁆ ∈ G'.gPosTwo := by
      rw [f.map_lie]
      exact G'.posOne_posOne_mem_posTwo hX' hY'
    rw [Submodule.mem_comap] at ⊢
    exact h₃
  negOne_negOne_mem_negTwo := by
    intro X Y hX hY
    have hX' : f X ∈ G'.gNegOne := by
      rw [Submodule.mem_comap] at hX
      exact hX
    have hY' : f Y ∈ G'.gNegOne := by
      rw [Submodule.mem_comap] at hY
      exact hY
    have h₃ : f ⁅X, Y⁆ ∈ G'.gNegTwo := by
      rw [f.map_lie]
      exact G'.negOne_negOne_mem_negTwo hX' hY'
    rw [Submodule.mem_comap] at ⊢
    exact h₃

/-- **Five-Graded Colimit Cone Bracket Transport Theorem**:
1. The composition of grade-preserving Lie bonding/inclusion homomorphisms
   `bond_nm : L_n →ₗ⁅ℝ⁆ L_m` and `ι_m : L_m →ₗ⁅ℝ⁆ L_∞` is grade-preserving.
2. When `ι_m.comp bond_nm = ι_n`, applying `bond_nm` followed by `ι_m` to any homogeneous
   pair $(X, Y)$ in grades $(-1, +1)$, $(-2, +2)$, $(+1, +1)$, or $(-1, -1)$ transports their
   bracket into the exact target grade of the colimit five-grading `G_inf`:
   $$\iota_m(b_{nm}(\lbrack X, Y \rbrack)) = \lbrack \iota_n(X), \iota_n(Y) \rbrack \in G_{\infty, i+j}.$$ -/
theorem fiveGrading_colimit_cone_bracket_transport
    {Ln Lm Linf : Type*}
    [LieRing Ln] [LieAlgebra ℝ Ln]
    [LieRing Lm] [LieAlgebra ℝ Lm]
    [LieRing Linf] [LieAlgebra ℝ Linf]
    (Gn : FiveGrading Ln) (Gm : FiveGrading Lm) (Ginf : FiveGrading Linf)
    (bond_nm : Ln →ₗ⁅ℝ⁆ Lm) (ι_n : Ln →ₗ⁅ℝ⁆ Linf) (ι_m : Lm →ₗ⁅ℝ⁆ Linf)
    (h_bond : IsFiveGradePreservingLieHom Gn Gm bond_nm)
    (h_ιm : IsFiveGradePreservingLieHom Gm Ginf ι_m)
    (h_cone : ∀ x : Ln, ι_m (bond_nm x) = ι_n x)
    (X_m1 Y_m1 X_p1 Y_p1 X_m2 X_p2 : Ln)
    (hXm1 : X_m1 ∈ Gn.gNegOne) (hYm1 : Y_m1 ∈ Gn.gNegOne)
    (hXp1 : X_p1 ∈ Gn.gPosOne) (hYp1 : Y_p1 ∈ Gn.gPosOne)
    (hXm2 : X_m2 ∈ Gn.gNegTwo) (hXp2 : X_p2 ∈ Gn.gPosTwo) :
    IsFiveGradePreservingLieHom Gn Ginf (ι_m.comp bond_nm) ∧
    (ι_m (bond_nm ⁅X_m1, X_p1⁆) = ⁅ι_n X_m1, ι_n X_p1⁆ ∧
     ⁅ι_n X_m1, ι_n X_p1⁆ ∈ Ginf.gZero) ∧
    (ι_m (bond_nm ⁅X_m2, X_p2⁆) = ⁅ι_n X_m2, ι_n X_p2⁆ ∧
     ⁅ι_n X_m2, ι_n X_p2⁆ ∈ Ginf.gZero) ∧
    (ι_m (bond_nm ⁅X_p1, Y_p1⁆) = ⁅ι_n X_p1, ι_n Y_p1⁆ ∧
     ⁅ι_n X_p1, ι_n Y_p1⁆ ∈ Ginf.gPosTwo) ∧
    (ι_m (bond_nm ⁅X_m1, Y_m1⁆) = ⁅ι_n X_m1, ι_n Y_m1⁆ ∧
     ⁅ι_n X_m1, ι_n Y_m1⁆ ∈ Ginf.gNegTwo) := by
  have h_comp : IsFiveGradePreservingLieHom Gn Ginf (ι_m.comp bond_nm) := by
    refine ⟨fun x hx => h_ιm.1 _ (h_bond.1 x hx),
            fun x hx => h_ιm.2.1 _ (h_bond.2.1 x hx),
            fun x hx => h_ιm.2.2.1 _ (h_bond.2.2.1 x hx),
            fun x hx => h_ιm.2.2.2.1 _ (h_bond.2.2.2.1 x hx),
            fun x hx => h_ιm.2.2.2.2 _ (h_bond.2.2.2.2 x hx)⟩
  have h_ιn_m1 : ι_n X_m1 ∈ Ginf.gNegOne := by
    rw [← h_cone X_m1]
    exact h_ιm.2.1 _ (h_bond.2.1 X_m1 hXm1)
  have h_ιn_ym1 : ι_n Y_m1 ∈ Ginf.gNegOne := by
    rw [← h_cone Y_m1]
    exact h_ιm.2.1 _ (h_bond.2.1 Y_m1 hYm1)
  have h_ιn_p1 : ι_n X_p1 ∈ Ginf.gPosOne := by
    rw [← h_cone X_p1]
    exact h_ιm.2.2.2.1 _ (h_bond.2.2.2.1 X_p1 hXp1)
  have h_ιn_yp1 : ι_n Y_p1 ∈ Ginf.gPosOne := by
    rw [← h_cone Y_p1]
    exact h_ιm.2.2.2.1 _ (h_bond.2.2.2.1 Y_p1 hYp1)
  have h_ιn_m2 : ι_n X_m2 ∈ Ginf.gNegTwo := by
    rw [← h_cone X_m2]
    exact h_ιm.1 _ (h_bond.1 X_m2 hXm2)
  have h_ιn_p2 : ι_n X_p2 ∈ Ginf.gPosTwo := by
    rw [← h_cone X_p2]
    exact h_ιm.2.2.2.2 _ (h_bond.2.2.2.2 X_p2 hXp2)
  refine ⟨h_comp, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [h_cone ⁅X_m1, X_p1⁆, ι_n.map_lie]
  · exact Ginf.negOne_posOne_mem_zero h_ιn_m1 h_ιn_p1
  · rw [h_cone ⁅X_m2, X_p2⁆, ι_n.map_lie]
  · exact Ginf.bracket_negTwo_posTwo (ι_n X_m2) (ι_n X_p2) h_ιn_m2 h_ιn_p2
  · rw [h_cone ⁅X_p1, Y_p1⁆, ι_n.map_lie]
  · exact Ginf.posOne_posOne_mem_posTwo h_ιn_p1 h_ιn_yp1
  · rw [h_cone ⁅X_m1, Y_m1⁆, ι_n.map_lie]
  · exact Ginf.negOne_negOne_mem_negTwo h_ιn_m1 h_ιn_ym1

/-- **Five-Graded Maurer–Cartan Flatness Decomposition, Freudenthal Jacobi Closure, & Koszul Supertrace Laws**:
1. **The Five Maurer–Cartan Equations**:
   A 5-graded Cartan connection jet $\Omega = \Omega_{-2} + \Omega_{-1} + \Omega_0 + \Omega_{+1} + \Omega_{+2}$
   is flat (`mcCurvatureTower J_mc = (0, 0, 0, 0, 0)`) if and only if all five homogeneous
   components satisfy:
   $$\begin{aligned}
   d\Omega_{-2} + [\Omega_0 \wedge \Omega_{-2}] &= -\tfrac{1}{2}[\Omega_{-1} \wedge \Omega_{-1}], \\
   d\Omega_{-1} + [\Omega_0 \wedge \Omega_{-1}] &= -[\Omega_{+1} \wedge \Omega_{-2}], \\
   d\Omega_0 + \tfrac{1}{2}[\Omega_0 \wedge \Omega_0] &= -([\Omega_{-1} \wedge \Omega_{+1}] + [\Omega_{-2} \wedge \Omega_{+2}]), \\
   d\Omega_{+1} + [\Omega_0 \wedge \Omega_{+1}] &= -[\Omega_{-1} \wedge \Omega_{+2}], \\
   d\Omega_{+2} + [\Omega_0 \wedge \Omega_{+2}] &= -\tfrac{1}{2}[\Omega_{+1} \wedge \Omega_{+1}].
   \end{aligned}$$
2. **Freudenthal 5-Graded Jacobi Closure**:
   The $(-1, -1, +1)$, $(+1, +1, -1)$, and $(0, 0, 0)$ homogeneous Jacobiators on
   `FiveGradedCarrier D` vanish identically.
3. **Koszul Cohomological Supertrace Invariance**:
   For any square-zero boundary supercharges $Q_{\mathrm{bos}}^2 = 0$ on $M_2(\mathbb{R})$ and
   $Q_{\mathrm{fer}}^2 = 0$ on $M_3(\mathbb{R})$, every commutator coboundary has vanishing
   $(2\vert 3)$ supertrace (`superTrace23 = 0`). -/
theorem five_graded_maurer_cartan_equations_and_koszul_supertrace_laws
    {J_freud : Type*} [AddCommGroup J_freud] [Module ℝ J_freud]
    (D : CubicJordanDatum J_freud)
    (c₁ c₂ c₃ : FreudenthalCharge J_freud)
    (T₁ T₂ T₃ : SymplecticTKKZero D)
    (J_mc : FiveGradedMaurerCartanJet ℝ)
    (A_bos Q_bos M_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D_fer Q_fer M_fer : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ_bos : Q_bos * Q_bos = 0)
    (hQ_fer : Q_fer * Q_fer = 0) :
    (mcCurvatureTower J_mc = (0, 0, 0, 0, 0) ↔
      (J_mc.dOmega_m2 + J_mc.br_0_m2 = -J_mc.br_m1_m1_half ∧
       J_mc.dOmega_m1 + J_mc.br_0_m1 = -J_mc.br_p1_m2 ∧
       J_mc.dOmega_0 + J_mc.br_0_0_half = -(J_mc.br_m1_p1 + J_mc.br_m2_p2) ∧
       J_mc.dOmega_p1 + J_mc.br_0_p1 = -J_mc.br_m1_p2 ∧
       J_mc.dOmega_p2 + J_mc.br_0_p2 = -J_mc.br_p1_p1_half)) ∧
    (fiveJacobiator D (injChargeMinus D c₁) (injChargeMinus D c₂) (injChargePlus D c₃) = 0 ∧
     fiveJacobiator D (injChargePlus D c₁) (injChargePlus D c₂) (injChargeMinus D c₃) = 0 ∧
     fiveJacobiator D (injSympZero D T₁) (injSympZero D T₂) (injSympZero D T₃) = 0) ∧
    (superTrace23 (Q_bos * M_bos - M_bos * Q_bos) (Q_fer * M_fer - M_fer * Q_fer) = 0 ∧
     superTrace23
       (A_bos + (Q_bos * M_bos - M_bos * Q_bos))
       (D_fer + (Q_fer * M_fer - M_fer * Q_fer)) =
       superTrace23 A_bos D_fer) := by
  have h_str :=
    homological_context_supertrace_invariance A_bos Q_bos M_bos D_fer Q_fer M_fer hQ_bos hQ_fer
  exact ⟨mcCurvatureTower_flat_iff_source_laws J_mc,
    ⟨jacobi_chargeMinus_chargeMinus_chargePlus D c₁ c₂ c₃,
     jacobi_chargePlus_chargePlus_chargeMinus D c₁ c₂ c₃,
     jacobi_zero_zero_zero D T₁ T₂ T₃⟩,
    ⟨h_str.2.1, h_str.2.2⟩⟩

/-!
## Section 2: Hestenes–Krein Readout, Hessian-Compatible Dikin Transport, & Conditional KMS Remainders
-/

/-- **Hessian-compatible Dikin-set transport and conditional remainder estimate**:
Given spaces $E_n, E_m, E_\infty$ equipped with potentials
$\Phi_n, \Phi_m, \Phi_\infty$ and continuous linear maps $\iota_{nm} : E_n \toL[\mathbb{R}] E_m$,
$\iota_n : E_n \toL[\mathbb{R}] E_\infty$, $\iota_m : E_m \toL[\mathbb{R}] E_\infty$ satisfying
$\iota_m \circ \iota_{nm} = \iota_n$ and Hessian compatibility:
1. **Dikin Metric Isometry ($\iota_{nm}^* g_m = g_n \implies \|\iota_{nm} v\|_{\iota_{nm} x} = \|v\|_x$)**:
   `dikinHessianNorm Φ_m (ι_nm x) (ι_nm v) = dikinHessianNorm Φ_n x v` and
   `dikinHessianNorm Φ_inf (ι_n x) (ι_n v) = dikinHessianNorm Φ_n x v`.
2. **Dikin Ellipsoid Preservation ($\iota_{nm}(E_n(x)) \subseteq E_m(\iota_{nm} x)$)**:
   `ι_nm '' dikinEllipsoid Φ_n x ⊆ dikinEllipsoid Φ_m (ι_nm x)` and for every $y \in E_n(x)$,
   its two-stage image $\iota_m(\iota_{nm} y) = \iota_n y$ lies in the colimit Dikin ellipsoid
   `dikinEllipsoid Φ_inf (ι_n x)`.
3. **Filtered Hestenes–Krein Colimit Readout & Conditional KMS Remainder Bound**:
   On any `C : HestenesKreinCone`, compatible stage readouts satisfy
   `stageBarrier readout k z = limitBarrier limitReadout (C.ι k z)`, and a supplied exponential
   satisfying `HasBregmanQuadraticBound` obeys `‖expOp (ε • K) - 1 - ε • K‖ ≤ ε ^ 2` when
   `‖K‖ = 1` and `|ε| ≤ 1`. The ellipsoid results are Hessian-sublevel transport statements;
   they do not assert self-concordance, positive definiteness, or containment in a feasible
   domain. The last component remains conditional on the supplied bound and does not construct
   `expOp`. -/
theorem dikin_hessian_compatible_cone_transport
    {En Em Einf : Type*}
    [NormedAddCommGroup En] [NormedSpace ℝ En]
    [NormedAddCommGroup Em] [NormedSpace ℝ Em]
    [NormedAddCommGroup Einf] [NormedSpace ℝ Einf]
    (Φn : En → ℝ) (Φm : Em → ℝ) (Φinf : Einf → ℝ)
    (ι_nm : En →L[ℝ] Em) (ι_n : En →L[ℝ] Einf) (ι_m : Em →L[ℝ] Einf)
    (x v y : En)
    (h_cone : ∀ z : En, ι_m (ι_nm z) = ι_n z)
    (hHess_nm : ∀ u w : En,
      InfoGeometry.Geometry.LegendreDifferential.hessianMap Φm (ι_nm x) (ι_nm u) (ι_nm w) =
        InfoGeometry.Geometry.LegendreDifferential.hessianMap Φn x u w)
    (hHess_m : ∀ u w : Em,
      InfoGeometry.Geometry.LegendreDifferential.hessianMap Φinf (ι_m (ι_nm x)) (ι_m u) (ι_m w) =
        InfoGeometry.Geometry.LegendreDifferential.hessianMap Φm (ι_nm x) u w)
    (hy : y ∈ dikinEllipsoid Φn x)
    {C : HestenesKreinCone}
    (readout : ∀ k, InfoGeometry.Krein.DoubledSpace (C.Base k) → ℝ)
    (limitReadout : InfoGeometry.Krein.DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ k z, readout k z = limitReadout (C.ι k z))
    (k : ℕ) (z : InfoGeometry.Krein.DoubledSpace (C.Base k))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (expOp : ExpOp H) (K : H →L[ℝ] H)
    (hquad : HasBregmanQuadraticBound expOp K) (hK_norm : ‖K‖ = 1)
    (ε : ℝ) (hε : |ε| ≤ 1) :
    (dikinHessianNorm Φm (ι_nm x) (ι_nm v) = dikinHessianNorm Φn x v ∧
     dikinHessianNorm Φinf (ι_n x) (ι_n v) = dikinHessianNorm Φn x v) ∧
    (ι_nm '' dikinEllipsoid Φn x ⊆ dikinEllipsoid Φm (ι_nm x) ∧
     ι_m (ι_nm y) ∈ dikinEllipsoid Φinf (ι_n x)) ∧
    (stageBarrier readout k z = limitBarrier limitReadout (C.ι k z) ∧
     ‖expOp (ε • K) - (1 : H →L[ℝ] H) - (ε • K)‖ ≤ ε ^ 2) := by
  have hHess_n : ∀ u w : En,
      InfoGeometry.Geometry.LegendreDifferential.hessianMap Φinf (ι_n x) (ι_n u) (ι_n w) =
        InfoGeometry.Geometry.LegendreDifferential.hessianMap Φn x u w := by
    intro u w
    rw [← h_cone x, ← h_cone u, ← h_cone w, hHess_m (ι_nm u) (ι_nm w), hHess_nm u w]
  have h_norm_nm := hessianCompatible_dikinNorm_eq Φn Φm ι_nm x v hHess_nm
  have h_norm_n := hessianCompatible_dikinNorm_eq Φn Φinf ι_n x v hHess_n
  have h_ell_nm := hessianCompatible_maps_dikinEllipsoid Φn Φm ι_nm x hHess_nm
  have h_ell_n := hessianCompatible_maps_dikinEllipsoid Φn Φinf ι_n x hHess_n
  have hy_inf : ι_m (ι_nm y) ∈ dikinEllipsoid Φinf (ι_n x) := by
    rw [h_cone y]
    exact h_ell_n ⟨y, hy, rfl⟩
  exact ⟨⟨h_norm_nm, h_norm_n⟩,
    ⟨h_ell_nm, hy_inf⟩,
    ⟨stageBarrier_eq_limitBarrier readout limitReadout hreadout k z,
     bregman_remainder_bounded_of_quadratic_bound expOp K hquad hK_norm ε hε⟩⟩

/-- Transport-constrained Drazin–Dikin attention quadratic form
$Q(v) = D^2\Phi(x)[G v, G v] = \operatorname{hessianQuadratic}\Phi(x, G v)$ evaluated on the
potential response $u = G v$ of an attention forcing $v$ under a Drazin Green operator $G = L^D$. -/
noncomputable def drazinDynamicQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x : E) (G_drazin : E →L[ℝ] E) (v : E) : ℝ :=
  hessianQuadratic potential x (G_drazin v)

/-- Transport-constrained dynamic attention Dikin ellipsoid
$\mathcal{E}_x^{\mathrm{dyn}} = \{v \mid Q(v) = D^2\Phi(x)[L^D v, L^D v] < 1\}$. -/
def drazinDynamicEllipsoid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x : E) (G_drazin : E →L[ℝ] E) : Set E :=
  {v | drazinDynamicQuadratic potential x G_drazin v < 1}

/-- **Drazin Attention Projector Decomposition & Colimit Drazin–Dikin Quadratic Form Preservation**:
1. **Index-One Drazin Attention Projector Laws (`DikinDrazinBridge.AttentionLaplacian`)**:
   For any attention Laplacian $L$ and Drazin Green operator $G = L^D$ satisfying
   `IsDrazinInverse L G` and the index-one condition $L G L = L$, the dynamic projector
   $P_{\mathrm{dyn}} = L G$ and harmonic projector $P_{\mathrm{harm}} = 1 - L G$ satisfy
   $P_{\mathrm{dyn}}^2 = P_{\mathrm{dyn}}$, $P_{\mathrm{dyn}} + P_{\mathrm{harm}} = 1$,
   $P_{\mathrm{dyn}} P_{\mathrm{harm}} = 0$, and $L P_{\mathrm{harm}} = 0$.
2. **Colimit Intertwining of the Drazin–Dikin Attention Quadratic Form ($Q_m(\iota_{nm} v) = Q_n(v)$)**:
   Whenever a bonding map $\iota_{nm} : E_n \toL[\mathbb{R}] E_m$ intertwines the Drazin Green
   operators ($\forall w,\; \iota_{nm}(G_n w) = G_m(\iota_{nm} w)$) and preserves the barrier
   Hessian at $x$, it preserves the Drazin–Dikin attention quadratic form:
   $$\operatorname{drazinDynamicQuadratic}\Phi_m(\iota_{nm} x, G_m, \iota_{nm} v) =
     \operatorname{drazinDynamicQuadratic}\Phi_n(x, G_n, v)$$
   and maps the stage-$n$ transport-constrained Dikin ellipsoid into the stage-$m$ ellipsoid:
   $$\iota_{nm}(\mathcal{E}_n^{\mathrm{dyn}}(x)) \subseteq \mathcal{E}_m^{\mathrm{dyn}}(\iota_{nm} x).$$ -/
theorem drazin_attention_projector_and_colimit_dikin_preservation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L_att G_att : V →ₗ[ℝ] V)
    (hD : OperatorSurgery.IsDrazinInverse L_att G_att)
    (hIndexOne : L_att * G_att * L_att = L_att)
    {En Em : Type*}
    [NormedAddCommGroup En] [NormedSpace ℝ En]
    [NormedAddCommGroup Em] [NormedSpace ℝ Em]
    (Φn : En → ℝ) (Φm : Em → ℝ)
    (Gn : En →L[ℝ] En) (Gm : Em →L[ℝ] Em)
    (ι_nm : En →L[ℝ] Em)
    (x v : En)
    (h_intertwine : ∀ w : En, ι_nm (Gn w) = Gm (ι_nm w))
    (hHess_nm : ∀ u w : En,
      InfoGeometry.Geometry.LegendreDifferential.hessianMap Φm (ι_nm x) (ι_nm u) (ι_nm w) =
        InfoGeometry.Geometry.LegendreDifferential.hessianMap Φn x u w) :
    (AttentionLaplacian.dynamicProjector L_att G_att *
       AttentionLaplacian.dynamicProjector L_att G_att =
         AttentionLaplacian.dynamicProjector L_att G_att ∧
     AttentionLaplacian.dynamicProjector L_att G_att +
       AttentionLaplacian.harmonicProjector L_att G_att = 1 ∧
     AttentionLaplacian.dynamicProjector L_att G_att *
       AttentionLaplacian.harmonicProjector L_att G_att = 0 ∧
     L_att * AttentionLaplacian.harmonicProjector L_att G_att = 0) ∧
    drazinDynamicQuadratic Φm (ι_nm x) Gm (ι_nm v) =
      drazinDynamicQuadratic Φn x Gn v ∧
    ι_nm '' drazinDynamicEllipsoid Φn x Gn ⊆
      drazinDynamicEllipsoid Φm (ι_nm x) Gm := by
  have h_quad :
      drazinDynamicQuadratic Φm (ι_nm x) Gm (ι_nm v) =
        drazinDynamicQuadratic Φn x Gn v := by
    unfold drazinDynamicQuadratic hessianQuadratic
    rw [← h_intertwine v, hHess_nm (Gn v) (Gn v)]
  refine ⟨⟨AttentionLaplacian.dynamicProjector_idempotent hD,
           AttentionLaplacian.projectors_partition L_att G_att,
           AttentionLaplacian.dynamic_harmonic_disjoint hD,
           AttentionLaplacian.laplacian_annihilates_harmonic hD hIndexOne⟩,
          h_quad, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  change drazinDynamicQuadratic Φm (ι_nm x) Gm (ι_nm w) < 1
  unfold drazinDynamicQuadratic hessianQuadratic
  rw [← h_intertwine w, hHess_nm (Gn w) (Gn w)]
  exact hw

/-!
## Section 3: Hestenes' 2D Planar Geometric Derivative $\partial = e_1 \partial_x + e_2 \partial_y$ and the Monogenic / Cauchy–Riemann Equivalence
-/

/-- First orthonormal planar Clifford generator
$e_1 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in M_2(\mathbb{R})$ ($e_1^2 = I_2$). -/
def planarCliffordE1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

/-- Second orthonormal planar Clifford generator
$e_2 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in M_2(\mathbb{R})$ ($e_2^2 = I_2$). -/
def planarCliffordE2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

/-- Oriented 2D unit bivector (pseudoscalar)
$I = e_1 e_2 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix} \in M_2(\mathbb{R})$ ($I^2 = -I_2$). -/
def planarBivectorI : Matrix (Fin 2) (Fin 2) ℝ :=
  planarCliffordE1 * planarCliffordE2

/-- The orthonormal planar Clifford generators $e_1$ and $e_2$ do not commute in $M_2(\mathbb{R})$:
`planarCliffordE1 * planarCliffordE2 ≠ planarCliffordE2 * planarCliffordE1`. -/
theorem planarCliffordE1_mul_planarCliffordE2_ne_comm :
    planarCliffordE1 * planarCliffordE2 ≠ planarCliffordE2 * planarCliffordE1 := by
  intro h_comm
  have h01 : (planarCliffordE1 * planarCliffordE2) 0 1 =
      (planarCliffordE2 * planarCliffordE1) 0 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h_comm
  revert h01
  simp [planarCliffordE1, planarCliffordE2, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- **Planar Clifford & Bivector Complex Structure Identities**:
$e_1^2 = I_2$, $e_2^2 = I_2$, $e_1 e_2 + e_2 e_1 = 0$, and the unit bivector $I = e_1 e_2$
satisfies $I^2 = -I_2$ (realizing `RealRotorPhaseAxis` on $M_2(\mathbb{R})$). -/
theorem planarClifford_bivector_relations :
    planarCliffordE1 ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    planarCliffordE2 ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    planarCliffordE1 * planarCliffordE2 + planarCliffordE2 * planarCliffordE1 = 0 ∧
    planarBivectorI ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, planarCliffordE1, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, planarCliffordE2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planarCliffordE1, planarCliffordE2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, planarBivectorI, planarCliffordE1, planarCliffordE2,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Planar even-grade multivector $F(u, v) = u I_2 + v I \in \mathrm{Cl}^+(2, 0) \subset M_2(\mathbb{R})$. -/
def planarEvenMultivector (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  u • (1 : Matrix (Fin 2) (Fin 2) ℝ) + v • planarBivectorI

/-- Hestenes' 2D geometric vector derivative
$\partial F = e_1 (\partial_x F) + e_2 (\partial_y F)$ acting on a first-order planar jet
$(\partial_x u, \partial_y u, \partial_x v, \partial_y v)$. -/
def hestenesVectorDeriv (du_dx du_dy dv_dx dv_dy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  planarCliffordE1 * planarEvenMultivector du_dx dv_dx +
    planarCliffordE2 * planarEvenMultivector du_dy dv_dy

/-- Explicit $(0, 0)$ entry of Hestenes' 2D vector derivative:
$(\partial F)_{00} = \partial_x u - \partial_y v$. -/
theorem hestenesVectorDeriv_apply_00 (du_dx du_dy dv_dx dv_dy : ℝ) :
    hestenesVectorDeriv du_dx du_dy dv_dx dv_dy 0 0 = du_dx - dv_dy := by
  change (planarCliffordE1 * planarEvenMultivector du_dx dv_dx) 0 0 +
    (planarCliffordE2 * planarEvenMultivector du_dy dv_dy) 0 0 = du_dx - dv_dy
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [planarCliffordE1, planarCliffordE2, planarEvenMultivector, planarBivectorI]
  ring

/-- Explicit $(0, 1)$ entry of Hestenes' 2D vector derivative:
$(\partial F)_{01} = \partial_x v + \partial_y u$. -/
theorem hestenesVectorDeriv_apply_01 (du_dx du_dy dv_dx dv_dy : ℝ) :
    hestenesVectorDeriv du_dx du_dy dv_dx dv_dy 0 1 = dv_dx + du_dy := by
  change (planarCliffordE1 * planarEvenMultivector du_dx dv_dx) 0 1 +
    (planarCliffordE2 * planarEvenMultivector du_dy dv_dy) 0 1 = dv_dx + du_dy
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [planarCliffordE1, planarCliffordE2, planarEvenMultivector, planarBivectorI]

/-- **Hestenes' Monogenic Factorization & Cauchy–Riemann Equivalence Theorem**:
1. The 2D vector derivative factors through $e_1$ as
   $$\partial F = e_1 \left((\partial_x u - \partial_y v) I_2 + (\partial_x v + \partial_y u) I\right),$$
2. $\partial F = 0$ holds if and only if the Cauchy–Riemann equations
   $\partial_x u = \partial_y v \land \partial_y u = -\partial_x v$ hold,
3. Whenever the Cauchy–Riemann equations hold, the bivector-weighted interior integrand
   $I \cdot (\partial F)$ vanishes identically. -/
theorem hestenes_monogenic_factorization_and_cauchy_riemann
    (du_dx du_dy dv_dx dv_dy : ℝ) :
    hestenesVectorDeriv du_dx du_dy dv_dx dv_dy =
      planarCliffordE1 * planarEvenMultivector (du_dx - dv_dy) (dv_dx + du_dy) ∧
    (hestenesVectorDeriv du_dx du_dy dv_dx dv_dy = 0 ↔
      (du_dx = dv_dy ∧ du_dy = -dv_dx)) ∧
    ((du_dx = dv_dy ∧ du_dy = -dv_dx) →
      planarBivectorI * hestenesVectorDeriv du_dx du_dy dv_dx dv_dy = 0) := by
  have h_fac :
      hestenesVectorDeriv du_dx du_dy dv_dx dv_dy =
        planarCliffordE1 * planarEvenMultivector (du_dx - dv_dy) (dv_dx + du_dy) := by
    ext i j
    change (planarCliffordE1 * planarEvenMultivector du_dx dv_dx) i j +
      (planarCliffordE2 * planarEvenMultivector du_dy dv_dy) i j =
      (planarCliffordE1 * planarEvenMultivector (du_dx - dv_dy) (dv_dx + du_dy)) i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      (simp [planarEvenMultivector, planarBivectorI, planarCliffordE1, planarCliffordE2];
       try ring)
  have h_iff :
      hestenesVectorDeriv du_dx du_dy dv_dx dv_dy = 0 ↔
        (du_dx = dv_dy ∧ du_dy = -dv_dx) := by
    constructor
    · intro h_zero
      have h00 : hestenesVectorDeriv du_dx du_dy dv_dx dv_dy 0 0 = 0 :=
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h_zero
      have h01 : hestenesVectorDeriv du_dx du_dy dv_dx dv_dy 0 1 = 0 :=
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h_zero
      rw [hestenesVectorDeriv_apply_00] at h00
      rw [hestenesVectorDeriv_apply_01] at h01
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h_u, h_v⟩
      rw [h_fac, h_u, h_v, sub_self, add_neg_cancel]
      have h_em_zero : planarEvenMultivector 0 0 = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [planarEvenMultivector]
      rw [h_em_zero, Matrix.mul_zero]
  refine ⟨h_fac, h_iff, ?_⟩
  intro h_cr
  rw [h_iff.mpr h_cr, Matrix.mul_zero]

/-!
## Section 4: Real Incidence Stokes Pairing, Two-Sided Boundary Jumps, & Krein Discontinuity Readout
-/

/-- Finite real Stokes pairing $\langle \partial_1 c, \varphi \rangle_0 = \langle c, \delta^0 \varphi \rangle_1$
inherited from `RealRotorGaussHestenesBridge.incidence_real_stokes_gauss`. -/
theorem real_boundary_coboundary_pairing
    {A : DAG.TripleSystem}
    [DecidableEq A.Obj]
    (c : RealIncidenceChains.Incidence.OneChains A)
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A) :
    RealStokesGaussHomology.Incidence.pairZero
        (A := A)
        (RealIncidenceChains.Incidence.boundaryOne A c)
        φ =
      RealStokesGaussHomology.Incidence.pairOne
        (A := A) c
        (RealIncidenceHomology.Incidence.zeroCoboundary φ) :=
  incidence_real_stokes_gauss c φ

/-- Conditional on the supplied `RealGaussStokesReadout` law, a vanishing bulk readout implies a
vanishing boundary readout (`G.bulkReadout c = 0 → G.boundaryReadout (G.boundaryOf c) = 0`). -/
theorem boundary_zero_of_bulk_zero
    {Chain Boundary : Type*}
    (G : RealGaussStokesReadout Chain Boundary)
    (c : Chain)
    (h : G.bulkReadout c = 0) :
    G.boundaryReadout (G.boundaryOf c) = 0 := by
  rw [G.gaussStokes_law c]
  exact h

/-- Oriented two-sided real boundary jump $\operatorname{Jump}(b_+, b_-) = b_+ - b_-$. -/
def boundaryJump (forward backward : ℝ) : ℝ :=
  forward - backward

/-- Symmetric two-sided principal-value average $\operatorname{PV}(b_+, b_-) = \frac{1}{2}(b_+ + b_-)$. -/
def boundaryPrincipalValue (forward backward : ℝ) : ℝ :=
  (forward + backward) / 2

/-- Vanishing of the two-sided boundary jump when forward and backward traces coincide. -/
@[simp]
theorem boundaryJump_self (a : ℝ) :
    boundaryJump a a = 0 := by
  simp [boundaryJump]

/-- Orientation reversal negates the two-sided boundary jump. -/
theorem boundaryJump_antisymm (a b : ℝ) :
    boundaryJump a b = -boundaryJump b a := by
  unfold boundaryJump
  ring

/-- Telescoping additivity of the two-sided boundary jump across an intermediate sheet. -/
theorem boundaryJump_add (a b c : ℝ) :
    boundaryJump a c = boundaryJump a b + boundaryJump b c := by
  unfold boundaryJump
  ring

/-- Primal causal sheet projection $[x]_{T^+} = (x_+, 0)$ on $\mathcal{K}_n = \mathbb{R}^n \times \mathbb{R}^n$. -/
def kreinSheetPlus {n : ℕ} (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (x.1, 0)

/-- Dual retrocausal sheet projection $[x]_{T^-} = (0, x_-)$ on $\mathcal{K}_n = \mathbb{R}^n \times \mathbb{R}^n$. -/
def kreinSheetMinus {n : ℕ} (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (0, x.2)

/-- Algebraic Stokes boundary jump $[x]_{T^+} - [x]_{T^-} = (x_+, -x_-)$ across the two Krein sheets. -/
def kreinBoundaryJump {n : ℕ} (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  kreinSheetPlus x - kreinSheetMinus x

/-- Off-diagonal split-Krein neutral metric
$g_{\mathcal{K}}((x_+, x_-), (y_+, y_-)) = \sum_i (x_{+,i} y_{-,i} + x_{-,i} y_{+,i})$. -/
def splitKreinMetric {n : ℕ} (x y : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i : Fin n, (x.1 i * y.2 i + x.2 i * y.1 i)

/-- **Two-Sheeted Krein Boundary Discontinuity & Two-Sided Boundary Trace Reconstruction**:
1. **Two-Sheeted Krein Decomposition & Null Isotropy**:
   Every state decomposes as $x = [x]_{T^+} + [x]_{T^-}$, both sheets $T^\pm$ are totally isotropic
   under `splitKreinMetric`, and pairing $[x]_{T^+}$ with $\operatorname{Jump}(y)$ extracts
   $-\sum_i x_{+,i} y_{-,i}$.
2. **Conditional Two-Sided Boundary Trace Decomposition**:
   Whenever upper and lower boundary traces $\mathcal{B}_+, \mathcal{B}_-$ have discontinuity
   $\operatorname{Disc}(\mathcal{A}) = \operatorname{boundaryJump}(\mathcal{B}_+, \mathcal{B}_-)$
   and symmetric average $\operatorname{PV}(\mathcal{A}) = \operatorname{boundaryPrincipalValue}(\mathcal{B}_+, \mathcal{B}_-)$,
   the boundary traces decompose as
   $\mathcal{B}_\pm = \operatorname{PV}(\mathcal{A}) \pm \frac{1}{2}\operatorname{Disc}(\mathcal{A})$. -/
theorem krein_two_sheeted_boundary_discontinuity_laws
    {n : ℕ} (x y : (Fin n → ℝ) × (Fin n → ℝ))
    (B_plus B_minus discA pvA : ℝ)
    (h_disc : discA = boundaryJump B_plus B_minus)
    (h_pv : pvA = boundaryPrincipalValue B_plus B_minus) :
    (kreinSheetPlus x + kreinSheetMinus x = x ∧
     kreinBoundaryJump x = (x.1, -x.2) ∧
     kreinBoundaryJump (kreinBoundaryJump x) = x) ∧
    (splitKreinMetric (kreinSheetPlus x) (kreinSheetPlus y) = 0 ∧
     splitKreinMetric (kreinSheetMinus x) (kreinSheetMinus y) = 0) ∧
    splitKreinMetric (kreinSheetPlus x) (kreinBoundaryJump y) =
      -∑ i : Fin n, x.1 i * y.2 i ∧
    (B_plus = pvA + discA / 2 ∧
     B_minus = pvA - discA / 2 ∧
     B_plus - B_minus = discA) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩⟩
  · ext i <;> simp [kreinSheetPlus, kreinSheetMinus]
  · ext i <;> simp [kreinBoundaryJump, kreinSheetPlus, kreinSheetMinus]
  · ext i <;> simp [kreinBoundaryJump, kreinSheetPlus, kreinSheetMinus]
  · unfold splitKreinMetric kreinSheetPlus
    simp
  · unfold splitKreinMetric kreinSheetMinus
    simp
  · unfold splitKreinMetric kreinSheetPlus kreinBoundaryJump kreinSheetMinus
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change x.1 i * (0 - y.2 i) + 0 * (y.1 i - 0) = -(x.1 i * y.2 i)
    ring
  · rw [h_pv, h_disc]
    unfold boundaryPrincipalValue boundaryJump
    ring
  · rw [h_pv, h_disc]
    unfold boundaryPrincipalValue boundaryJump
    ring
  · rw [h_disc]
    rfl

/-!
## Section 5: Nilpotent Exponential Truncation, Jordan Monodromy Readout, Shirokov Determinants, & Fisher–Souriau Laplacian Gauge Kernel
-/

/-- Rank-2 nilpotent Jordan generator
$N_{\mathrm{Jordan}} = S_+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \in M_2(\mathbb{C})$. -/
def jordanResidueNilpotent : Matrix (Fin 2) (Fin 2) ℂ :=
  Splus

/-- First-order truncated exponential $\exp_{\le 1}(\theta N) = I_2 + \theta N \in M_2(\mathbb{C})$
for a square-zero nilpotent operator $N^2 = 0$. -/
def nilpotentExpTrunc (θ : ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + θ • N

/-- For any square-zero matrix $N^2 = 0$ in $M_2(\mathbb{C})$, the truncated nilpotent exponential
$\exp_{\le 1}(\theta N) = I_2 + \theta N$ satisfies the exact additive group homomorphism law:
$$\exp_{\le 1}(\theta_1 N) \cdot \exp_{\le 1}(\theta_2 N) = \exp_{\le 1}((\theta_1 + \theta_2) N).$$ -/
theorem nilpotentExpTrunc_mul_of_sq_zero
    (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) (θ₁ θ₂ : ℂ) :
    nilpotentExpTrunc θ₁ N * nilpotentExpTrunc θ₂ N =
      nilpotentExpTrunc (θ₁ + θ₂) N := by
  unfold nilpotentExpTrunc
  have h_expand :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + θ₁ • N) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) + θ₂ • N) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) + θ₁ • N + θ₂ • N + θ₁ • (N * (θ₂ • N)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two]; ring)
  rw [h_expand, mul_smul_comm, hN, smul_zero, smul_zero, add_zero, add_assoc, ← add_smul]

/-- The chiral unipotent shear composes additively:
`unipotentChiralShear p * unipotentChiralShear q = unipotentChiralShear (p + q)`. -/
theorem jordan_shear_composition (p q : ℂ) :
    unipotentChiralShear p * unipotentChiralShear q =
      unipotentChiralShear (p + q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [unipotentChiralShear, Splus, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- A double winding of the chiral unipotent shear doubles the shear parameter:
`unipotentChiralShear p * unipotentChiralShear p = unipotentChiralShear (2 * p)`. -/
theorem jordan_double_winding (p : ℂ) :
    unipotentChiralShear p * unipotentChiralShear p =
      unipotentChiralShear (2 * p) := by
  rw [jordan_shear_composition]
  congr 1
  ring

/-- Exact algebraic extraction of the nilpotent contribution from the unipotent shear without
analytic limits: `unipotentChiralShear p - I_2 = p • Splus`. -/
theorem jordan_exact_algebraic_readout (p : ℂ) :
    unipotentChiralShear p - (1 : Matrix (Fin 2) (Fin 2) ℂ) = p • Splus := by
  simp [unipotentChiralShear]

/-- **Jordan–Hadjiivanov Monodromy Readout & Shirokov Matrix-Free Determinants**:
1. **Nilpotent Generator & Double-Winding Tensor Readout**:
   $N_{\mathrm{Jordan}}^2 = 0$, $N_{\mathrm{Jordan}} \neq 0$,
   $U(p)^2 = I_2 + (2p) N_{\mathrm{Jordan}}$, and on the tensor square
   `standardJordanObject ⊗[ℂ] standardJordanObject` the double action of `residueCheckedR p`
   equals the identity if and only if $p = 0$.
2. **Conditional Monodromy-to-Operator Readout**:
   Whenever a monodromy operator `monNabla` is identified with the truncated nilpotent
   exponential $\operatorname{Mon}(\nabla) = \exp_{\le 1}(2p \, N_{\mathrm{Jordan}})$ and
   $(2p) \cdot \mathrm{invTwoP} = 1$, the nilpotent generator $N_{\mathrm{Jordan}}$ is uniquely
   recovered via $\mathrm{invTwoP} \bullet (\operatorname{Mon}(\nabla) - I_2) = N_{\mathrm{Jordan}}$.
3. **Quadratic & Ternary Shirokov Matrix-Free Determinants**:
   In both $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$ and $C\ell_2^{\frac{1}{3}} \cong M_3(\mathbb{C})$,
   the determinant is extracted purely algebraically via internal Clifford conjugation and
   Shirokov's $\underline{U}$ adjugate. -/
theorem jordan_hadjiivanov_algebraic_residue_and_shirokov_det_laws
    (p invTwoP : ℂ) (hp_inv : (2 * p) * invTwoP = 1)
    (monNabla : Matrix (Fin 2) (Fin 2) ℂ)
    (h_mon_corr : monNabla = nilpotentExpTrunc (2 * p) jordanResidueNilpotent)
    (u0 u1 u2 u12 : ℝ)
    (U₃ : Matrix (Fin 3) (Fin 3) ℂ) :
    (jordanResidueNilpotent ^ 2 = 0 ∧
     jordanResidueNilpotent ≠ 0 ∧
     (((residueCheckedR p).trans (residueCheckedR p)).toLinearMap = LinearMap.id ↔ p = 0)) ∧
    (unipotentChiralShear p * unipotentChiralShear p =
       (1 : Matrix (Fin 2) (Fin 2) ℂ) + (2 * p) • jordanResidueNilpotent ∧
     invTwoP • (monNabla - (1 : Matrix (Fin 2) (Fin 2) ℂ)) = jordanResidueNilpotent) ∧
    (cl11Multivector u0 u1 u2 u12 * cl11CliffordConj u0 u1 u2 u12 =
       cl11DetScalar u0 u1 u2 u12 • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
     U₃ * ternaryShirokovAdjugate U₃ =
       Matrix.det U₃ • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
  have h_nil_sq : jordanResidueNilpotent ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, jordanResidueNilpotent, Splus, Matrix.mul_apply, Fin.sum_univ_two]
  have h_nil_ne : jordanResidueNilpotent ≠ 0 := by
    intro h_zero
    have h01 : jordanResidueNilpotent 0 1 = 0 :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h_zero
    revert h01
    simp [jordanResidueNilpotent, Splus]
  have h_double :
      unipotentChiralShear p * unipotentChiralShear p =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) + (2 * p) • jordanResidueNilpotent := by
    rw [jordan_double_winding p]
    rfl
  have h_res :
      invTwoP • (monNabla - (1 : Matrix (Fin 2) (Fin 2) ℂ)) = jordanResidueNilpotent := by
    rw [h_mon_corr]
    unfold nilpotentExpTrunc
    rw [add_sub_cancel_left, smul_smul, mul_comm invTwoP (2 * p), hp_inv, one_smul]
  exact ⟨⟨h_nil_sq, h_nil_ne, residueCheckedR_double_eq_id_iff p⟩,
    ⟨h_double, h_res⟩,
    ⟨(cl11_shirokov_det_formula u0 u1 u2 u12).1,
     (ternaryShirokov_adjugate_mul_eq_det U₃).1⟩⟩

/-- **Souriau–Massieu Stokes Evaluation of Surprisal & Chentsov Cumulant Variance**:
For any logit state $s : \mathrm{Fin}\, m \to \mathbb{R}$, coordinate index $j_0 : \mathrm{Fin}\, m$,
perturbation $\delta s : \mathrm{Fin}\, m \to \mathbb{R}$, and uniform shift $c \in \mathbb{R}$:
1. **Exact Coordinate Derivative ($\partial \Phi / \partial s_{j_0} = A_{j_0}(s)$)**:
   `HasDerivAt (fun t : ℝ => souriauMassieuPotential (Function.update s j₀ t)) (souriauAttentionWeight s j₀) (s j₀)`
   holds, with linear moment pairing `souriauMomentMap s δs = ∑ j, souriauAttentionWeight s j * δs j`,
2. **Exact Boundary Shift Evaluation ($\Delta \Phi = c$)**:
   $\Phi(s + c\mathbf{1}) - \Phi(s) = c$,
3. **Second Chentsov Cumulant / Fisher–Souriau Variance**:
   $$\sum_{j,k} \delta s_j g^S_{jk}(s) \delta s_k =
     \sum_j A_j(s) (\delta s_j - \operatorname{souriauMomentMap}(s, \delta s))^2 \ge 0.$$ -/
theorem souriau_massieu_stokes_surprisal_and_chentsov_cumulant_laws
    {m : ℕ} [Nonempty (Fin m)]
    (s δs : Fin m → ℝ) (j₀ : Fin m) (c : ℝ) :
    (HasDerivAt (fun t : ℝ => souriauMassieuPotential (Function.update s j₀ t))
       (souriauAttentionWeight s j₀) (s j₀) ∧
     souriauMomentMap s δs = ∑ j : Fin m, souriauAttentionWeight s j * δs j) ∧
    (souriauMassieuPotential (fun j => s j + c) - souriauMassieuPotential s = c) ∧
    (∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k =
       ∑ j : Fin m, souriauAttentionWeight s j * (δs j - souriauMomentMap s δs) ^ 2 ∧
     0 ≤ ∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k) := by
  have h_deriv := hasDerivAt_souriauMassieuPotential_coord s j₀
  have h_shift : souriauMassieuPotential (fun j => s j + c) - souriauMassieuPotential s = c := by
    rw [(souriauMassieu_shift_and_attention_scale_invariance s c j₀).1, add_sub_cancel_left]
  have h_cumulant := fisherSouriau_quadratic_eq_variance_and_nonneg s δs
  exact ⟨⟨h_deriv, rfl⟩, h_shift, h_cumulant⟩

/-- **Fisher–Souriau Attention Laplacian Gauge Kernel ($\ker H(s) = \mathbb{R}\mathbf{1}$) & Harmonic Score Transport**:
1. **Row-Sum Annihilation of Constant Vectors ($H(s)\mathbf{1} = 0$)**:
   For every coordinate $j$, $\sum_{k=1}^m H_{jk}(s) = 0$.
2. **Exact Characterization of the Quadratic Kernel ($\ker H(s) = \mathbb{R}\mathbf{1}$)**:
   Because every attention weight is strictly positive ($A_j(s) > 0$), the Fisher–Souriau
   Laplacian quadratic form vanishes on $\delta s$ if and only if $\delta s_j = \operatorname{souriauMomentMap}(s, \delta s)$
   for all $j$, which holds if and only if $\delta s$ is a constant gauge vector ($\exists c \in \mathbb{R}, \forall j, \delta s_j = c$).
3. **Harmonic Gauge Score Transport Invariance**:
   Whenever a score transformation $T : (\mathrm{Fin}\, m \to \mathbb{R}) \to (\mathrm{Fin}\, m \to \mathbb{R})$
   (such as a unipotent Jordan shear $U(a)s = s + a N s$) shifts scores by a constant gauge mode
   $T(s) - s = c\mathbf{1}$ (`∀ j, T s j = s j + c`), the Souriau–Massieu potential shifts by $+c$
   and all normalized attention weights are strictly preserved:
   $$\Phi(T(s)) = \Phi(s) + c \;\land\; \forall j,\; A_j(T(s)) = A_j(s).$$ -/
theorem fisher_souriau_laplacian_gauge_kernel_and_const_iff
    {m : ℕ} [Nonempty (Fin m)]
    (s δs : Fin m → ℝ) (j₀ : Fin m)
    (T : (Fin m → ℝ) → (Fin m → ℝ)) (c : ℝ)
    (hT : T s = fun j => s j + c) :
    (∑ k : Fin m, fisherSouriauHessian s j₀ k = 0) ∧
    (∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k = 0 ↔
      ∀ j : Fin m, δs j = souriauMomentMap s δs) ∧
    ((∀ j : Fin m, δs j = souriauMomentMap s δs) ↔
      ∃ c₀ : ℝ, ∀ j : Fin m, δs j = c₀) ∧
    (souriauMassieuPotential (T s) = souriauMassieuPotential s + c ∧
     ∀ j : Fin m, souriauAttentionWeight (T s) j = souriauAttentionWeight s j) := by
  have h_sum_one : ∑ k : Fin m, souriauAttentionWeight s k = 1 :=
    (massieu_free_entropy_legendre_identity s j₀).1
  have h_row : ∑ k : Fin m, fisherSouriauHessian s j₀ k = 0 := by
    simp only [fisherSouriauHessian, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [h_sum_one]
  have h_var := (fisherSouriau_quadratic_eq_variance_and_nonneg s δs).1
  have h_ker_iff :
      ∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k = 0 ↔
        ∀ j : Fin m, δs j = souriauMomentMap s δs := by
    rw [h_var]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (le_of_lt (souriauAttentionWeight_pos s j)) (sq_nonneg _))]
    constructor
    · intro h_all j
      have hj := h_all j (Finset.mem_univ j)
      have h_pos : souriauAttentionWeight s j ≠ 0 := ne_of_gt (souriauAttentionWeight_pos s j)
      rcases mul_eq_zero.mp hj with h_w | h_sq
      · exact False.elim (h_pos h_w)
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h_sq)
    · intro h_const j _
      rw [h_const j, sub_self, sq, mul_zero, mul_zero]
  have h_const_iff :
      (∀ j : Fin m, δs j = souriauMomentMap s δs) ↔
        ∃ c₀ : ℝ, ∀ j : Fin m, δs j = c₀ := by
    constructor
    · intro h_eq
      exact ⟨souriauMomentMap s δs, h_eq⟩
    · rintro ⟨c₀, hc₀⟩ j
      have h_mom : souriauMomentMap s δs = c₀ := by
        unfold souriauMomentMap
        have h_term : ∀ k : Fin m, souriauAttentionWeight s k * δs k = souriauAttentionWeight s k * c₀ :=
          fun k => by rw [hc₀ k]
        simp_rw [h_term, ← Finset.sum_mul, h_sum_one, one_mul]
      rw [hc₀ j, h_mom]
  refine ⟨h_row, h_ker_iff, h_const_iff, ?_⟩
  rw [hT]
  exact ⟨(souriauMassieu_shift_and_attention_scale_invariance s c j₀).1,
         fun j => (souriauMassieu_shift_and_attention_scale_invariance s c j).2⟩

end InfoGeometry.Synthesis.HestenesStokesAlgebraicBoundarySynthesis
