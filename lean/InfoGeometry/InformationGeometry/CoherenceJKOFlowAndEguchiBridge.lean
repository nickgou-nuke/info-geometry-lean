/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.InformationGeometry.CoherencePullbackMetricAndPalatiniConfinement
import InfoGeometry.OptimalTransport.OttoVillaniGradientFlow
import InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
import InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature
import InfoGeometry.Meta.ArchetypePipeline

/-!
# Coherence JKO Flow, Wootters–Eguchi Divergence, and Milnor–Dual Curvature Bridge

Canonical synthesis closing the remaining variational, information-geometric, and affine
curvature pathways connecting `InfoGeometry.Clifford.GradedGraceContraction`,
`InfoGeometry.InformationGeometry.CoherencePullbackMetricAndPalatiniConfinement`,
`InfoGeometry.OptimalTransport.OttoVillaniGradientFlow`,
`InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn`, and
`InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature`:

1. **Scaled Proximal JKO Resolvent & Otto–Villani Stationarity**:
   - Defines `jkoGraceResolvent Q τ` with step-size weights `(1 + τ * (φ^k - 1))⁻¹`, proves its
     exact completion of the square for `scaledParsimoniousJKO Q τ u₀ u`, proves global unique
     minimality and strong energy dissipation, recovers `graceOperator Q` at unit step `τ = 1`,
     derives 1D Otto–Villani gradient-flow stationarity via `OttoVillaniGradientFlow`, and pairs
     it with noncommutative `M₂(ℂ)` coherent-vs-Gibbs obstruction from
     `BlochBallUmegakiAndQuantumSpohn`.
2. **Wootters–Eguchi–Grace Second-Derivative Bridge**:
   - Defines `graceQuadraticDivergence` and `coherencePullbackDivergence`, proves positive
     definiteness and symmetry, constructs the orthonormal grade-1 blade embedding
     `woottersBladeEmbed`, equates its Euclidean and Grace norms to the 2nd derivative of
     KL divergence `eguchi_kl_right_secondDeriv`, and proves exact quadratic scaling of
     `coherencePullbackDivergence` along affine rays in `Cl(3,1)`.
3. **Milnor Octahedral Pair Symmetry & Noncommuting Dual-Connection Curvature**:
   - Proves Milnor's algebraic Riemann pair symmetry `R X Y Z W = R Z W X Y` and Ricci symmetry
     from pair skew-symmetries plus the first Bianchi identity, and bridges to
     `EguchiMetricsAndDualFlatCurvature.connCurvature_sum` on an explicit noncommuting
     `Module.End ℝ (Fin 2 → ℝ)` skew-connection tensor.

## Three-Bucket Audit Map
* **BUCKET 1 (Native kernel-checked definitions & theorems)**:
  - Scaled JKO resolvent, completion of the square, unique minimizer, energy dissipation,
    Otto–Villani 1D stationarity, Wootters–Eguchi KL second-derivative identity, Milnor pair &
    Ricci symmetry, and noncommuting dual-connection commutator witness.
* **BUCKET 2 (Reused repository owners)**:
  - `cliffordGradeProj`, `graceOperator`, `graceBladeInner`, `gradePenaltyEnergy`
    (`GradedGraceContraction`), `coherenceGraceMetricMatrix`, `canonicalLinearCoherence31`
    (`CoherencePullbackMetricAndPalatiniConfinement`), `otto_villani_gradient_flow`
    (`OttoVillaniGradientFlow`), `blochBall_matrix_noncommutative`, `coherent_not_commute_gibbs`
    (`BlochBallUmegakiAndQuantumSpohn`), `eguchi_kl_right_secondDeriv`, `connCurvature_sum`
    (`EguchiMetricsAndDualFlatCurvature`), and `TypedArchetype` (`ArchetypePipeline`).
* **BUCKET 3 (Explicit hypotheses / scope)**:
  - Variational optimality holds over finite-dimensional real Clifford algebras `Cl(Q)` with
    `τ > 0`; simplex derivatives use explicit interior curves `Q_stat : ℝ → ProbInterior (Fin n)`;
    Milnor pair symmetry assumes algebraic skew-symmetries and the first Bianchi identity.
-/

set_option autoImplicit false

namespace InfoGeometry.InformationGeometry.CoherenceJKOFlowAndEguchiBridge

open CliffordAlgebra
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.InformationGeometry.CoherencePullbackMetricAndPalatiniConfinement
open InfoGeometry.OptimalTransport.OttoVillaniGradientFlow
open InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
open InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry
open InfoGeometry.Statistical
open InfoGeometry.MetaCompiler
open scoped goldenRatio Matrix

section ScalarHelpers

private theorem scalar_scaled_jko_completion_repr (τ w x x₀ : ℝ)
    (hτ : τ ≠ 0) (hμ : 1 + τ * (w - 1) ≠ 0) :
    ((1 / 2 : ℝ) * ((w - 1) * x ^ 2) + (1 / (2 * τ)) * ((x - x₀) * (x - x₀))) -
        ((1 / 2 : ℝ) * ((w - 1) * ((1 + τ * (w - 1))⁻¹ * x₀) ^ 2) +
          (1 / (2 * τ)) * (((1 + τ * (w - 1))⁻¹ * x₀ - x₀) *
            ((1 + τ * (w - 1))⁻¹ * x₀ - x₀))) =
      (1 / (2 * τ)) *
        ((x - (1 + τ * (w - 1))⁻¹ * x₀) *
          ((1 + τ * (w - 1)) * x - (1 + τ * (w - 1)) * ((1 + τ * (w - 1))⁻¹ * x₀))) := by
  have hx0 : x₀ = (1 + τ * (w - 1)) * ((1 + τ * (w - 1))⁻¹ * x₀) := by
    rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul]
  generalize (1 + τ * (w - 1))⁻¹ * x₀ = y at hx0 ⊢
  subst hx0
  field_simp [hτ]
  ring

private theorem scalar_jko_weight_pos {τ w : ℝ} (hτ : 0 < τ) (hw : 1 ≤ w) :
    0 < 1 + τ * (w - 1) := by
  nlinarith [hτ, hw]

private theorem scalar_jko_weight_ge_one {τ w : ℝ} (hτ : 0 < τ) (hw : 1 ≤ w) :
    1 ≤ 1 + τ * (w - 1) := by
  nlinarith [hτ, hw]

private theorem scalar_add_mul_le_trans {a b c d : ℝ} (hid : a - b = c) (hmul : d ≤ c) :
    b + d ≤ a := by
  linarith [hid, hmul]

private theorem scalar_le_and_eq_zero {p q s : ℝ} (hlb : q + s ≤ p) (hnn : 0 ≤ s) :
    q ≤ p ∧ (p = q → s = 0) :=
  ⟨by linarith [hlb, hnn], fun hpq => by linarith [hlb, hnn, hpq]⟩

private theorem scalar_jko_dissip_rearrange {e₁ d e₀ : ℝ} (h : e₁ + d ≤ e₀ + 0) :
    e₁ + d ≤ e₀ := by
  linarith [h]

private theorem scalar_sub_sq_factor (a b : ℝ) (c : ℝ) (hid : a - b = c) :
    a = b + c := by
  linarith [hid]

private theorem scalar_line_quadratic_expand (a c b r : ℝ) :
    a + r * c + r * (c + r * b) = a + 2 * c * r + b * r ^ 2 := by
  ring

private theorem scalar_half_mul_two_mul (a b : ℝ) :
    (1 / 2 : ℝ) * (a * (2 * b)) = a * b := by
  ring

private theorem scalar_neg_twice_mul (c a t : ℝ) :
    (1 / 2 : ℝ) * (-t * (-t * a)) = (t ^ 2 / 2) * a := by
  have _ : c = c := rfl
  ring

private theorem scalar_stiff_quad_scale (r t b : ℝ) :
    r * (t * (t * b)) = r * b * t ^ 2 := by
  ring

private theorem scalar_wootters_term (p dq : ℝ) (hp : 0 < p) :
    (dq / Real.sqrt p) * (dq / Real.sqrt p) = dq * dq / p := by
  rw [div_mul_div_comm, Real.mul_self_sqrt (le_of_lt hp)]

private theorem scalar_wootters_half_deriv (dq p : ℝ) (hp : 0 < p) :
    2 * (dq / (2 * Real.sqrt p)) = dq / Real.sqrt p := by
  have hsq : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hsq]

private theorem scalar_half_sq_mul (t q : ℝ) :
    (1 / 2 : ℝ) * ((t * q) * (t * q)) = (t ^ 2 / 2) * (q * q) := by
  ring

private theorem scalar_milnor_octahedral
    {r_xyzw r_yzxw r_zxyw r_yzwx r_zwyx r_wyzx
     r_zwxy r_wxzy r_xzwy r_wxyz r_xywz r_ywxz : ℝ}
    (b1 : r_xyzw + r_yzxw + r_zxyw = 0)
    (b2 : r_yzwx + r_zwyx + r_wyzx = 0)
    (b3 : r_zwxy + r_wxzy + r_xzwy = 0)
    (b4 : r_wxyz + r_xywz + r_ywxz = 0)
    (s1 : r_yzwx = -r_yzxw)
    (s2 : r_wxyz = -r_wxzy)
    (s3 : r_xywz = -r_xyzw)
    (s4 : r_zwyx = -r_zwxy)
    (s5 : r_xzwy = r_zxyw)
    (s6 : r_ywxz = r_wyzx) :
    r_xyzw = r_zwxy := by
  linarith [b1, b2, b3, b4, s1, s2, s3, s4, s5, s6]

private theorem scalar_half_sub_neg (a : ℝ) :
    (1 / 2 : ℝ) * (a - -a) = a := by
  ring

private theorem scalar_smul_grace_term (c w r : ℝ) :
    w * ((c * r) * (c * r)) = c * (c * (w * (r * r))) := by
  ring

private theorem scalar_quad_hasDerivAt (a c b : ℝ) :
    HasDerivAt (fun s : ℝ => a + c * s + b * s ^ 2) c 0 := by
  have h1 : HasDerivAt (fun s : ℝ => a + c * s) (0 + (0 * 0 + c * 1)) 0 :=
    (hasDerivAt_const (0 : ℝ) a).add
      ((hasDerivAt_const (0 : ℝ) c).mul (hasDerivAt_id (0 : ℝ)))
  have h2 : HasDerivAt (fun s : ℝ => b * s ^ 2) (0 * (0 : ℝ) ^ 2 + b * ((2 : ℕ) * (0 : ℝ) ^ (2 - 1))) 0 :=
    (hasDerivAt_const (0 : ℝ) b).mul (hasDerivAt_pow 2 (0 : ℝ))
  have h12 := h1.add h2
  have hval : (0 + (0 * 0 + c * 1)) + (0 * (0 : ℝ) ^ 2 + b * ((2 : ℕ) * (0 : ℝ) ^ (2 - 1))) = c := by
    ring
  rwa [hval] at h12

end ScalarHelpers

section NoncommutativityWitnesses

/-- Closed `M₂(ℂ)` noncommutativity witness supporting the quantum Bloch–Gibbs JKO bridge. -/
theorem mat2c_jko_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  obtain ⟨A, B, hne⟩ := blochBall_matrix_noncommutative
  exact ⟨A, B, hne⟩

/-- Closed noncommutativity witness for `Module.End ℝ (Fin 2 → ℝ)`. -/
theorem moduleEnd_fin2_noncommutative :
    ∃ A B : Module.End ℝ (Fin 2 → ℝ), A * B ≠ B * A := by
  let A : Module.End ℝ (Fin 2 → ℝ) :=
    { toFun := fun v => ![v 1, 0]
      map_add' := fun u v => by ext i; fin_cases i <;> simp
      map_smul' := fun r v => by ext i; fin_cases i <;> simp }
  let B : Module.End ℝ (Fin 2 → ℝ) :=
    { toFun := fun v => ![v 0, 0]
      map_add' := fun u v => by ext i; fin_cases i <;> simp
      map_smul' := fun r v => by ext i; fin_cases i <;> simp }
  refine ⟨A, B, ?_⟩
  intro hEq
  have hEval := congrArg (fun f : Module.End ℝ (Fin 2 → ℝ) => f ![0, 1] 0) hEq
  dsimp [A, B, Module.End.mul_apply] at hEval
  exact one_ne_zero hEval.symm

end NoncommutativityWitnesses

/-! ## Pathway 4: Scaled Proximal JKO Resolvent, Otto–Villani Stationarity & Quantum Noncommutativity -/

section ScaledProximalJKOFlow

/-- Grade-`k` resolvent eigenvalue `(1 + τ * (φ^k - 1))⁻¹` for step size `τ`. -/
noncomputable def jkoResolventWeight (τ : ℝ) (k : ℕ) : ℝ :=
  (1 + τ * (φ ^ (k : ℤ) - 1))⁻¹

/-- Step-size-`τ` JKO proximal Grace resolvent operator on `CliffordAlgebra Q`:
`R_{Q,τ} = ∑_{k=0}^n (1 + τ * (φ^k - 1))⁻¹ Π_k`. -/
noncomputable def jkoGraceResolvent {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (τ : ℝ) :
    CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q :=
  ∑ k ∈ Finset.range (n + 1), (jkoResolventWeight τ k) • cliffordGradeProj Q k

/-- Associated step-size-`τ` grade stiffness operator
`S_{Q,τ} = ∑_{k=0}^n (1 + τ * (φ^k - 1)) Π_k`. -/
noncomputable def jkoStiffnessOperator {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (τ : ℝ) :
    CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q :=
  ∑ k ∈ Finset.range (n + 1), (1 + τ * (φ ^ (k : ℤ) - 1)) • cliffordGradeProj Q k

/-- Scaled JKO proximal Parsimonious Flow objective for step size `τ`:
`J_{Q,τ}(u₀; u) = E(u) + (1 / (2τ)) ‖u - u₀‖²`. -/
noncomputable def scaledParsimoniousJKO {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (τ : ℝ) (u₀ u : CliffordAlgebra Q) : ℝ :=
  gradePenaltyEnergy Q u + (1 / (2 * τ)) * cliffordBladeInner Q (u - u₀) (u - u₀)

theorem repr_jkoGraceResolvent {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (τ : ℝ)
    (u : CliffordAlgebra Q) (S : Finset (Fin n)) :
    (cliffordBladeBasis Q).repr (jkoGraceResolvent Q τ u) S =
      jkoResolventWeight τ S.card * (cliffordBladeBasis Q).repr u S := by
  have hlt : S.card < n + 1 := Nat.lt_succ_of_le (by simpa using S.card_le_univ)
  dsimp [jkoGraceResolvent]
  rw [LinearMap.sum_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single S.card]
  · simp only [LinearMap.smul_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      repr_cliffordGradeProj, ite_true]
  · intro k _ hkS
    simp only [LinearMap.smul_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      repr_cliffordGradeProj]
    split_ifs with hcard
    · exact (hkS.symm hcard).elim
    · rw [mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hlt)).elim

theorem repr_jkoStiffnessOperator {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (τ : ℝ)
    (u : CliffordAlgebra Q) (S : Finset (Fin n)) :
    (cliffordBladeBasis Q).repr (jkoStiffnessOperator Q τ u) S =
      (1 + τ * (φ ^ (S.card : ℤ) - 1)) * (cliffordBladeBasis Q).repr u S := by
  have hlt : S.card < n + 1 := Nat.lt_succ_of_le (by simpa using S.card_le_univ)
  dsimp [jkoStiffnessOperator]
  rw [LinearMap.sum_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single S.card]
  · simp only [LinearMap.smul_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      repr_cliffordGradeProj, ite_true]
  · intro k _ hkS
    simp only [LinearMap.smul_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      repr_cliffordGradeProj]
    split_ifs with hcard
    · exact (hkS.symm hcard).elim
    · rw [mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hlt)).elim

/-- At unit JKO step size `τ = 1`, `jkoGraceResolvent Q 1` recovers the canonical golden Grace
contraction `graceOperator Q` identically. -/
theorem jkoGraceResolvent_unit_step {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    jkoGraceResolvent Q 1 = graceOperator Q := by
  refine LinearMap.ext fun u => ?_
  apply (cliffordBladeBasis Q).repr.injective
  ext S
  rw [repr_jkoGraceResolvent, repr_graceOperator]
  dsimp [jkoResolventWeight]
  rw [one_mul, add_sub_cancel, zpow_neg]

/-- **Scaled Completion of the Square**:
for every `τ > 0`, the excess JKO objective above `jkoGraceResolvent Q τ u₀` factors through
the positive-definite stiffness inner product `(1 / (2τ)) ⟨u - R_{Q,τ} u₀, S_{Q,τ}(u - R_{Q,τ} u₀)⟩`. -/
theorem scaledParsimoniousJKO_sub_resolvent {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {τ : ℝ} (hτ : 0 < τ) (u₀ u : CliffordAlgebra Q) :
    scaledParsimoniousJKO Q τ u₀ u -
        scaledParsimoniousJKO Q τ u₀ (jkoGraceResolvent Q τ u₀) =
      (1 / (2 * τ)) *
        cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀)
          (jkoStiffnessOperator Q τ (u - jkoGraceResolvent Q τ u₀)) := by
  dsimp [scaledParsimoniousJKO]
  rw [gradePenaltyEnergy_eq_repr_sum, gradePenaltyEnergy_eq_repr_sum]
  dsimp only [cliffordBladeInner, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [repr_jkoGraceResolvent, repr_jkoStiffnessOperator, map_sub, Finsupp.coe_sub,
    Pi.sub_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hw : (1 : ℝ) ≤ φ ^ (S.card : ℤ) := by
    rw [zpow_natCast]
    exact one_le_pow₀ (le_of_lt Real.one_lt_goldenRatio)
  have hμ : 1 + τ * (φ ^ (S.card : ℤ) - 1) ≠ 0 := ne_of_gt (scalar_jko_weight_pos hτ hw)
  dsimp [jkoResolventWeight]
  exact scalar_scaled_jko_completion_repr τ (φ ^ (S.card : ℤ))
    ((cliffordBladeBasis Q).repr u S) ((cliffordBladeBasis Q).repr u₀ S) (ne_of_gt hτ) hμ

theorem scaledParsimoniousJKO_lower_bound {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {τ : ℝ} (hτ : 0 < τ) (u₀ u : CliffordAlgebra Q) :
    scaledParsimoniousJKO Q τ u₀ (jkoGraceResolvent Q τ u₀) +
        (1 / (2 * τ)) *
          cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀) (u - jkoGraceResolvent Q τ u₀) ≤
      scaledParsimoniousJKO Q τ u₀ u := by
  have hid := scaledParsimoniousJKO_sub_resolvent Q hτ u₀ u
  have hcoeff_nonneg : (0 : ℝ) ≤ 1 / (2 * τ) := by positivity
  have hstiff :
      cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀) (u - jkoGraceResolvent Q τ u₀) ≤
        cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀)
          (jkoStiffnessOperator Q τ (u - jkoGraceResolvent Q τ u₀)) := by
    dsimp only [cliffordBladeInner, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [repr_jkoStiffnessOperator]
    refine Finset.sum_le_sum fun S _ => ?_
    have hw : (1 : ℝ) ≤ φ ^ (S.card : ℤ) := by
      rw [zpow_natCast]
      exact one_le_pow₀ (le_of_lt Real.one_lt_goldenRatio)
    have hge : (1 : ℝ) ≤ 1 + τ * (φ ^ (S.card : ℤ) - 1) :=
      scalar_jko_weight_ge_one hτ hw
    rw [mul_left_comm ((cliffordBladeBasis Q).repr (u - jkoGraceResolvent Q τ u₀) S)
      (1 + τ * (φ ^ (S.card : ℤ) - 1)) _]
    simpa using mul_le_mul_of_nonneg_right hge (mul_self_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hstiff hcoeff_nonneg
  exact scalar_add_mul_le_trans hid hmul

/-- **Unique Global Minimizer of the Scaled JKO Functional**:
for any `τ > 0`, `jkoGraceResolvent Q τ u₀` is the unique global minimizer of
`scaledParsimoniousJKO Q τ u₀`. -/
theorem jkoGraceResolvent_is_unique_minimizer {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {τ : ℝ} (hτ : 0 < τ) (u₀ u : CliffordAlgebra Q) :
    scaledParsimoniousJKO Q τ u₀ (jkoGraceResolvent Q τ u₀) ≤
        scaledParsimoniousJKO Q τ u₀ u ∧
      (scaledParsimoniousJKO Q τ u₀ u =
          scaledParsimoniousJKO Q τ u₀ (jkoGraceResolvent Q τ u₀) ↔
        u = jkoGraceResolvent Q τ u₀) := by
  have hlb := scaledParsimoniousJKO_lower_bound Q hτ u₀ u
  have hnn :
      0 ≤ cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀) (u - jkoGraceResolvent Q τ u₀) :=
    cliffordBladeInner_self_nonneg Q _
  have hinv_pos : (0 : ℝ) < 1 / (2 * τ) := by positivity
  have hterm_nonneg :
      0 ≤ (1 / (2 * τ)) *
        cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀) (u - jkoGraceResolvent Q τ u₀) :=
    mul_nonneg (le_of_lt hinv_pos) hnn
  obtain ⟨hle, himp⟩ := scalar_le_and_eq_zero hlb hterm_nonneg
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    have hzero :
        cliffordBladeInner Q (u - jkoGraceResolvent Q τ u₀) (u - jkoGraceResolvent Q τ u₀) = 0 :=
      (mul_eq_zero.mp (himp heq)).resolve_left (ne_of_gt hinv_pos)
    exact sub_eq_zero.mp ((cliffordBladeInner_self_eq_zero Q _).mp hzero)
  · rintro rfl
    rfl

/-- **Strong Discrete JKO Energy-Dissipation Inequality**:
every step of `jkoGraceResolvent Q τ` decreases `gradePenaltyEnergy` by at least
`(1 / (2τ)) ‖u₁ - u₀‖²`. -/
theorem gradePenaltyEnergy_jko_dissipation {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {τ : ℝ} (hτ : 0 < τ) (u₀ : CliffordAlgebra Q) :
    gradePenaltyEnergy Q (jkoGraceResolvent Q τ u₀) +
        (1 / (2 * τ)) *
          cliffordBladeInner Q (jkoGraceResolvent Q τ u₀ - u₀) (jkoGraceResolvent Q τ u₀ - u₀) ≤
      gradePenaltyEnergy Q u₀ := by
  have hmin := (jkoGraceResolvent_is_unique_minimizer Q hτ u₀ u₀).1
  dsimp [scaledParsimoniousJKO] at hmin
  have hzero : cliffordBladeInner Q (u₀ - u₀) (u₀ - u₀) = 0 := by
    simp only [sub_self, map_zero]
  rw [hzero, mul_zero] at hmin
  exact scalar_jko_dissip_rearrange hmin

private theorem cliffordBladeInner_line_hasDerivAt {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (a b : CliffordAlgebra Q) :
    HasDerivAt (fun s : ℝ => cliffordBladeInner Q (a + s • b) (a + s • b))
      (2 * cliffordBladeInner Q a b) 0 := by
  have hExpand :
      (fun s : ℝ => cliffordBladeInner Q (a + s • b) (a + s • b)) =
        fun s : ℝ => cliffordBladeInner Q a a + (2 * cliffordBladeInner Q a b) * s +
          cliffordBladeInner Q b b * s ^ 2 := by
    ext s
    have hsym : cliffordBladeInner Q b a = cliffordBladeInner Q a b :=
      cliffordBladeInner_symm Q b a
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hsym]
    exact scalar_line_quadratic_expand _ _ _ _
  rw [hExpand]
  exact scalar_quad_hasDerivAt (cliffordBladeInner Q a a) (2 * cliffordBladeInner Q a b)
    (cliffordBladeInner Q b b)

private theorem gradePenaltyEnergy_line_hasDerivAt {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    HasDerivAt (fun s : ℝ => gradePenaltyEnergy Q (u + s • v))
      (∑ k ∈ Finset.range (n + 1),
        (φ ^ (k : ℤ) - 1) *
          cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v)) 0 := by
  dsimp [gradePenaltyEnergy]
  have hsum :
      HasDerivAt
        (fun s : ℝ => ∑ k ∈ Finset.range (n + 1),
          (φ ^ (k : ℤ) - 1) *
            cliffordBladeInner Q (cliffordGradeProj Q k (u + s • v))
              (cliffordGradeProj Q k (u + s • v)))
        (∑ k ∈ Finset.range (n + 1),
          (φ ^ (k : ℤ) - 1) *
            (2 * cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v))) 0 := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have hmap :
        (fun s : ℝ => (φ ^ (k : ℤ) - 1) *
          cliffordBladeInner Q (cliffordGradeProj Q k (u + s • v))
            (cliffordGradeProj Q k (u + s • v))) =
          fun s : ℝ => (φ ^ (k : ℤ) - 1) *
            cliffordBladeInner Q (cliffordGradeProj Q k u + s • cliffordGradeProj Q k v)
              (cliffordGradeProj Q k u + s • cliffordGradeProj Q k v) := by
      ext s
      rw [map_add, map_smul]
    rw [hmap]
    have hterm := (hasDerivAt_const (0 : ℝ) (φ ^ (k : ℤ) - 1)).mul
      (cliffordBladeInner_line_hasDerivAt Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v))
    rwa [zero_mul, zero_add] at hterm
  have hmul0 := (hasDerivAt_const (0 : ℝ) (1 / 2 : ℝ)).mul hsum
  rw [zero_mul, zero_add] at hmul0
  have hval :
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range (n + 1),
          (φ ^ (k : ℤ) - 1) *
            (2 * cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v)) =
        ∑ k ∈ Finset.range (n + 1),
          (φ ^ (k : ℤ) - 1) *
            cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact scalar_half_mul_two_mul _ _
  rwa [hval] at hmul0

/-- **Otto–Villani Gradient-Flow Stationarity & Discrete Velocity Emergence**:
along any directional variation `s ↦ jkoGraceResolvent Q τ u₀ + s • v`, the 1D slice of
`scaledParsimoniousJKO Q τ u₀` matches `OttoVillaniGradientFlow.jko_action`, satisfies the
exact Otto–Villani Euler–Lagrange equation `otto_villani_gradient_flow`, and obeys
`discrete_time_velocity_emergence`. -/
theorem jkoGraceResolvent_otto_villani_stationarity {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {τ : ℝ} (hτ : 0 < τ) (u₀ v : CliffordAlgebra Q) :
    let u₁ := jkoGraceResolvent Q τ u₀
    let F : ℝ → ℝ := fun s => gradePenaltyEnergy Q (u₁ + s • v)
    let W_sq : ℝ → ℝ := fun s => cliffordBladeInner Q (u₁ + s • v - u₀) (u₁ + s • v - u₀)
    let F_grad : ℝ := ∑ k ∈ Finset.range (n + 1),
      (φ ^ (k : ℤ) - 1) *
        cliffordBladeInner Q (cliffordGradeProj Q k u₁) (cliffordGradeProj Q k v)
    let W_grad : ℝ := 2 * cliffordBladeInner Q (u₁ - u₀) v
    (∀ s : ℝ, scaledParsimoniousJKO Q τ u₀ (u₁ + s • v) = jko_action F W_sq τ s) ∧
      F_grad + (1 / (2 * τ)) * W_grad = 0 ∧
      W_grad / τ = -2 * F_grad := by
  intro u₁ F W_sq F_grad W_grad
  have hAction : ∀ s : ℝ, scaledParsimoniousJKO Q τ u₀ (u₁ + s • v) = jko_action F W_sq τ s := by
    intro s
    rfl
  have hF : HasDerivAt F F_grad 0 :=
    gradePenaltyEnergy_line_hasDerivAt Q u₁ v
  have hW : HasDerivAt W_sq W_grad 0 := by
    have hshift :
        W_sq = fun s : ℝ => cliffordBladeInner Q ((u₁ - u₀) + s • v) ((u₁ - u₀) + s • v) := by
      ext s
      have hvec : u₁ + s • v - u₀ = (u₁ - u₀) + s • v := by abel
      dsimp [W_sq]
      rw [hvec]
    rw [hshift]
    exact cliffordBladeInner_line_hasDerivAt Q (u₁ - u₀) v
  have hMinQuad :
      jko_action F W_sq τ = fun s : ℝ =>
        jko_action F W_sq τ 0 +
          ((1 / (2 * τ)) * cliffordBladeInner Q v (jkoStiffnessOperator Q τ v)) * s ^ 2 := by
    ext s
    have hSub :
        jko_action F W_sq τ s - jko_action F W_sq τ 0 =
          ((1 / (2 * τ)) * cliffordBladeInner Q v (jkoStiffnessOperator Q τ v)) * s ^ 2 := by
      have h0 : u₁ + (0 : ℝ) • v = u₁ := by simp
      rw [← hAction s, ← hAction 0, h0]
      rw [scaledParsimoniousJKO_sub_resolvent Q hτ u₀ (u₁ + s • v)]
      have hd : u₁ + s • v - jkoGraceResolvent Q τ u₀ = s • v := by
        change u₁ + s • v - u₁ = s • v
        abel
      have hd1 : jkoStiffnessOperator Q τ (s • v) = s • jkoStiffnessOperator Q τ v :=
        map_smul _ _ _
      rw [hd, hd1, map_smul, smul_eq_mul, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact scalar_stiff_quad_scale _ _ _
    exact scalar_sub_sq_factor _ _ _ hSub
  have hMinDeriv : HasDerivAt (jko_action F W_sq τ) 0 0 := by
    rw [hMinQuad]
    have hq := scalar_quad_hasDerivAt (jko_action F W_sq τ 0) 0
      ((1 / (2 * τ)) * cliffordBladeInner Q v (jkoStiffnessOperator Q τ v))
    simpa only [zero_mul, add_zero] using hq
  have hOV : F_grad + (1 / (2 * τ)) * W_grad = 0 :=
    otto_villani_gradient_flow F W_sq (fun _ => F_grad) (fun _ => W_grad) τ 0
      (ne_of_gt hτ) hF hW hMinDeriv
  have hVel : W_grad / τ = -2 * F_grad :=
    discrete_time_velocity_emergence F_grad τ W_grad (ne_of_gt hτ) hOV
  exact ⟨hAction, hOV, hVel⟩

/-- **Noncommutative Quantum Bloch-Gibbs Obstruction**:
in contrast to commutative real Euclidean/probability-simplex JKO flows, adding any nonzero
off-diagonal quantum coherence `z : ℂ` to `gibbsDensityC θ` yields a Hermitian matrix that fails
to commute with `gibbsDensityC θ` whenever `θ ≠ 0`. -/
theorem quantum_coherent_state_gibbs_noncommutativity
    {θ : ℝ} (hθ : θ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    let ρcoh : Matrix (Fin 2) (Fin 2) ℂ :=
      gibbsDensityC θ + Matrix.of ![![0, z], ![star z, 0]]
    ρcoh * gibbsDensityC θ ≠ gibbsDensityC θ * ρcoh := by
  intro ρcoh
  have h01 : ρcoh 0 1 ≠ 0 := by
    dsimp [ρcoh, gibbsDensityC, mat2]
    simpa using hz
  exact coherent_not_commute_gibbs hθ h01

end ScaledProximalJKOFlow

/-! ## Pathway 2: Wootters–Eguchi–Grace Second-Derivative Bridge -/

section WoottersEguchiGraceBridge

/-- Grace-weighted quadratic divergence `(1/2) ⟨u - v, G_Q (u - v)⟩` on `CliffordAlgebra Q`. -/
noncomputable def graceQuadraticDivergence {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) : ℝ :=
  (1 / 2 : ℝ) * graceBladeInner Q (u - v) (u - v)

/-- Pullback coherence divergence between parameter points `x, y : Fin n → ℝ`. -/
noncomputable def coherencePullbackDivergence {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x y : Fin n → ℝ) : ℝ :=
  graceQuadraticDivergence Q (Ψ x) (Ψ y)

/-- Positivity, symmetry, and faithfulness of `graceQuadraticDivergence`. -/
theorem graceQuadraticDivergence_pos_symm_faithful {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    0 ≤ graceQuadraticDivergence Q u v ∧
      graceQuadraticDivergence Q u v = graceQuadraticDivergence Q v u ∧
      (graceQuadraticDivergence Q u v = 0 ↔ u = v) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [graceQuadraticDivergence]
    exact mul_nonneg (by positivity) (graceBladeInner_self_nonneg Q _)
  · dsimp [graceQuadraticDivergence]
    have hneg : u - v = -(v - u) := by abel
    simp only [hneg, map_neg, LinearMap.neg_apply, neg_neg]
  · constructor
    · intro h
      dsimp [graceQuadraticDivergence] at h
      have h0 : graceBladeInner Q (u - v) (u - v) = 0 :=
        (mul_eq_zero.mp h).resolve_left (by norm_num)
      exact sub_eq_zero.mp ((graceBladeInner_self_eq_zero Q _).mp h0)
    · rintro rfl
      dsimp [graceQuadraticDivergence]
      rw [sub_self, map_zero, mul_zero]

/-- Grade-1 canonical Clifford blade embedding `v ↦ ∑ i, v i • cliffordBladeBasis Q {i}`. -/
noncomputable def woottersBladeEmbed {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    (Fin n → ℝ) →ₗ[ℝ] CliffordAlgebra Q where
  toFun v := ∑ i : Fin n, v i • cliffordBladeBasis Q ({i} : Finset (Fin n))
  map_add' u v := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

private theorem cliffordBladeInner_basis_pair {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (S T : Finset (Fin n)) :
    cliffordBladeInner Q (cliffordBladeBasis Q S) (cliffordBladeBasis Q T) =
      if S = T then 1 else 0 := by
  dsimp only [cliffordBladeInner, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single S]
  · simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul,
      Finsupp.single_apply, eq_comm]
  · intro R _ hRS
    simp only [Module.Basis.repr_self, Finsupp.single_eq_of_ne hRS, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ S)).elim

theorem cliffordBladeInner_woottersBladeEmbed {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : Fin n → ℝ) :
    cliffordBladeInner Q (woottersBladeEmbed Q u) (woottersBladeEmbed Q v) =
      ∑ i : Fin n, u i * v i := by
  dsimp [woottersBladeEmbed]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_eq_single j]
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hpair := cliffordBladeInner_basis_pair Q ({j} : Finset (Fin n)) ({j} : Finset (Fin n))
    simp only [ite_true] at hpair
    rw [hpair, mul_one, mul_comm]
  · intro i _ hij
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hne : ({i} : Finset (Fin n)) ≠ {j} := fun h => hij (Finset.singleton_injective h)
    have hpair := cliffordBladeInner_basis_pair Q ({i} : Finset (Fin n)) ({j} : Finset (Fin n))
    simp only [hne, ite_false] at hpair
    rw [hpair, mul_zero, mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ j)).elim

theorem graceBladeInner_woottersBladeEmbed {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : Fin n → ℝ) :
    graceBladeInner Q (woottersBladeEmbed Q u) (woottersBladeEmbed Q v) =
      φ ^ (-(1 : ℤ)) * ∑ i : Fin n, u i * v i := by
  have hGrace :
      ∀ j : Fin n,
        graceOperator Q (cliffordBladeBasis Q ({j} : Finset (Fin n))) =
          φ ^ (-(1 : ℤ)) • cliffordBladeBasis Q ({j} : Finset (Fin n)) := by
    intro j
    apply (cliffordBladeBasis Q).repr.injective
    ext S
    rw [repr_graceOperator, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hS : S = {j}
    · subst hS
      simp [Finset.card_singleton]
    · simp only [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with heq
      · exact (hS heq.symm).elim
      · rw [mul_zero, mul_zero]
  have hApply :
      graceOperator Q (woottersBladeEmbed Q v) =
        φ ^ (-(1 : ℤ)) • woottersBladeEmbed Q v := by
    dsimp [woottersBladeEmbed]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hGrace j, smul_smul, smul_smul, mul_comm]
  dsimp only [graceBladeInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  rw [hApply, map_smul, smul_eq_mul, cliffordBladeInner_woottersBladeEmbed]

/-- **Wootters–Eguchi–Grace Second-Derivative Bridge**:
along any twice-differentiable curve `Q_stat : ℝ → ProbInterior (Fin n)` with `Q_stat 0 = P`,
defining the Wootters tangent embedding `wVel i = dq 0 i / √(P.p i)`:
1. Each coordinate `s ↦ 2 * √((Q_stat s).p i)` has derivative `wVel i` at `s = 0`.
2. `‖woottersBladeEmbed Q wVel‖_blade² = d²/ds²|_{s=0} D_KL(P ∥ Q_stat s)`.
3. `⟨woottersBladeEmbed Q wVel, G_Q (woottersBladeEmbed Q wVel)⟩_blade = φ⁻¹ * d²/ds²|_{s=0} D_KL(P ∥ Q_stat s)`. -/
theorem wootters_eguchi_kl_grace_bridge {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (P : ProbInterior (Fin n)) (Q_stat : ℝ → ProbInterior (Fin n)) (hQ0 : Q_stat 0 = P)
    (dq : ℝ → Fin n → ℝ) (d2q : Fin n → ℝ)
    (hd1 : ∀ t i, HasDerivAt (fun s => (Q_stat s).p i) (dq t i) t)
    (hd2 : ∀ i, HasDerivAt (fun t => dq t i) (d2q i) 0) :
    let wVel : Fin n → ℝ := fun i => dq 0 i / Real.sqrt (P.p i)
    (∀ i : Fin n, HasDerivAt (fun s => 2 * Real.sqrt ((Q_stat s).p i)) (wVel i) 0) ∧
      cliffordBladeInner Q (woottersBladeEmbed Q wVel) (woottersBladeEmbed Q wVel) =
        deriv (deriv (fun s => ArakiDonald.relativeEntropy P.p (Q_stat s).p)) 0 ∧
      graceBladeInner Q (woottersBladeEmbed Q wVel) (woottersBladeEmbed Q wVel) =
        φ ^ (-(1 : ℤ)) *
          deriv (deriv (fun s => ArakiDonald.relativeEntropy P.p (Q_stat s).p)) 0 := by
  intro wVel
  have hDerivWootters :
      ∀ i : Fin n, HasDerivAt (fun s => 2 * Real.sqrt ((Q_stat s).p i)) (wVel i) 0 := by
    intro i
    have hpos : 0 < (Q_stat 0).p i := by
      rw [hQ0]
      exact P.pos i
    have hsqrt := ((hd1 0 i).sqrt (ne_of_gt hpos)).const_mul 2
    rw [hQ0] at hsqrt
    have hEq : 2 * (dq 0 i / (2 * Real.sqrt (P.p i))) = wVel i := by
      dsimp [wVel]
      exact scalar_wootters_half_deriv (dq 0 i) (P.p i) (P.pos i)
    rwa [hEq] at hsqrt
  have hEguchi := eguchi_kl_right_secondDeriv P Q_stat hQ0 dq d2q hd1 hd2
  have hNorm :
      cliffordBladeInner Q (woottersBladeEmbed Q wVel) (woottersBladeEmbed Q wVel) =
        fisherMetric P (dq 0) (dq 0) := by
    rw [cliffordBladeInner_woottersBladeEmbed]
    dsimp [fisherMetric, wVel]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact scalar_wootters_term (P.p i) (dq 0 i) (P.pos i)
  have hBlade :
      cliffordBladeInner Q (woottersBladeEmbed Q wVel) (woottersBladeEmbed Q wVel) =
        deriv (deriv (fun s => ArakiDonald.relativeEntropy P.p (Q_stat s).p)) 0 :=
    hNorm.trans hEguchi.symm
  have hGrace :
      graceBladeInner Q (woottersBladeEmbed Q wVel) (woottersBladeEmbed Q wVel) =
        φ ^ (-(1 : ℤ)) *
          deriv (deriv (fun s => ArakiDonald.relativeEntropy P.p (Q_stat s).p)) 0 := by
    rw [graceBladeInner_woottersBladeEmbed, ← cliffordBladeInner_woottersBladeEmbed, hBlade]
  exact ⟨hDerivWootters, hBlade, hGrace⟩

private theorem graceBladeInner_smul_smul {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (c : ℝ) (u : CliffordAlgebra Q) :
    graceBladeInner Q (c • u) (c • u) = c * (c * graceBladeInner Q u u) := by
  rw [graceBladeInner_eq_repr_sum, graceBladeInner_eq_repr_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact scalar_smul_grace_term c (φ ^ (-(S.card : ℤ))) ((cliffordBladeBasis Q).repr u S)

/-- Along any affine ray `x + t • v` in `ℝ⁴`, the canonical `Cl(3,1)` pullback coherence
divergence equals `(t² / 2) vᵀ g^G(x) v` identically. -/
theorem coherencePullbackDivergence_canonicalLinear31_ray (x v : Fin 4 → ℝ) (t : ℝ) :
    coherencePullbackDivergence Q31 canonicalLinearCoherence31 x (x + t • v) =
      (t ^ 2 / 2) *
        (star v ⬝ᵥ (coherenceGraceMetricMatrix Q31 canonicalLinearCoherence31 x *ᵥ v)) := by
  have hDiff :
      canonicalLinearCoherence31 x - canonicalLinearCoherence31 (x + t • v) =
        (-t) • fderiv ℝ canonicalLinearCoherence31 x v := by
    dsimp [canonicalLinearCoherence31]
    rw [(hasFDerivAt_canonicalLinearCoherence31 x).fderiv]
    rw [map_add, map_smul]
    abel_nf
    simp [neg_smul]
  dsimp only [coherencePullbackDivergence, graceQuadraticDivergence]
  rw [hDiff, graceBladeInner_smul_smul, ← coherenceGraceMetricMatrix_quadratic_form]
  exact scalar_neg_twice_mul (1 : ℝ) _ _

end WoottersEguchiGraceBridge

/-! ## Pathway 1: Milnor Octahedral Pair Symmetry & Noncommuting Dual-Connection Curvature -/

section MilnorOctahedralAndDualCurvatureBridge

/-- **Milnor's Octahedral Riemann Pair-Symmetry Theorem**:
any algebraic `(0,4)`-tensor `R` on `V` that is antisymmetric in its first two slots,
antisymmetric in its last two slots, and satisfies the algebraic first Bianchi identity
automatically satisfies full pair symmetry `R X Y Z W = R Z W X Y`. -/
theorem milnor_riemann_pair_symmetry {V : Type*} (R : V → V → V → V → ℝ)
    (hSkew12 : ∀ X Y Z W, R X Y Z W = -R Y X Z W)
    (hSkew34 : ∀ X Y Z W, R X Y Z W = -R X Y W Z)
    (hBianchi : ∀ X Y Z W, R X Y Z W + R Y Z X W + R Z X Y W = 0)
    (X Y Z W : V) :
    R X Y Z W = R Z W X Y :=
  scalar_milnor_octahedral
    (hBianchi X Y Z W)
    (hBianchi Y Z W X)
    (hBianchi Z W X Y)
    (hBianchi W X Y Z)
    (hSkew34 Y Z W X)
    (hSkew34 W X Y Z)
    (hSkew34 X Y W Z)
    (hSkew34 Z W Y X)
    ((hSkew12 X Z W Y).trans ((congrArg Neg.neg (hSkew34 Z X W Y)).trans (neg_neg _)))
    ((hSkew12 Y W X Z).trans ((congrArg Neg.neg (hSkew34 W Y X Z)).trans (neg_neg _)))

/-- Algebraic Ricci contraction over a finite frame `frame : Fin m → V`. -/
def ricciContraction {V : Type*} {m : ℕ} (frame : Fin m → V)
    (R : V → V → V → V → ℝ) (X Y : V) : ℝ :=
  ∑ i : Fin m, R (frame i) X Y (frame i)

/-- **Ricci Symmetry Theorem** derived directly from `milnor_riemann_pair_symmetry`. -/
theorem ricciContraction_symm {V : Type*} {m : ℕ} (frame : Fin m → V)
    (R : V → V → V → V → ℝ)
    (hSkew12 : ∀ X Y Z W, R X Y Z W = -R Y X Z W)
    (hSkew34 : ∀ X Y Z W, R X Y Z W = -R X Y W Z)
    (hBianchi : ∀ X Y Z W, R X Y Z W + R Y Z X W + R Z X Y W = 0)
    (X Y : V) :
    ricciContraction frame R X Y = ricciContraction frame R Y X := by
  dsimp [ricciContraction]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc R (frame i) X Y (frame i)
    _ = R Y (frame i) (frame i) X :=
        milnor_riemann_pair_symmetry R hSkew12 hSkew34 hBianchi (frame i) X Y (frame i)
    _ = -R (frame i) Y (frame i) X := hSkew12 Y (frame i) (frame i) X
    _ = -(-R (frame i) Y X (frame i)) := by rw [hSkew34 (frame i) Y (frame i) X]
    _ = R (frame i) Y X (frame i) := neg_neg _

/-- Explicit noncommuting skew-difference connection `(x : Fin 2 → ℝ) ↦ End(Fin 2 → ℝ)`
mapping `y ↦ ![x 0 * y 1, x 1 * y 0]`. -/
def noncommSkewConn : (Fin 2 → ℝ) →ₗ[ℝ] Module.End ℝ (Fin 2 → ℝ) where
  toFun x :=
    { toFun := fun y => ![x 0 * y 1, x 1 * y 0]
      map_add' := fun u v => by ext i; fin_cases i <;> simp [mul_add]
      map_smul' := fun r y => by ext i; fin_cases i <;> simp [mul_left_comm] }
  map_add' x₁ x₂ := by
    ext y i
    fin_cases i <;> simp [add_mul]
  map_smul' r x := by
    ext y i
    fin_cases i <;> simp [mul_assoc]

/-- Evaluating `connCurvature_sum` on `(conn, connStar) = (noncommSkewConn, -noncommSkewConn)`
produces a provably nonzero noncommuting endomorphism commutator `2 [K_e₀, K_e₁] ≠ 0`. -/
theorem noncommSkewConn_dual_curvature_sum_nonzero :
    let e0 : Fin 2 → ℝ := Pi.single 0 (1 : ℝ)
    let e1 : Fin 2 → ℝ := Pi.single 1 (1 : ℝ)
    connCurvature (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
        noncommSkewConn e0 e1 +
      connCurvature (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
        (-noncommSkewConn) e0 e1 =
      (2 : ℝ) • endComm (noncommSkewConn e0) (noncommSkewConn e1) ∧
    endComm (noncommSkewConn e0) (noncommSkewConn e1) ≠ 0 := by
  intro e0 e1
  have hSum :=
    connCurvature_sum (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
      noncommSkewConn (-noncommSkewConn) e0 e1
  have hMean : meanConn noncommSkewConn (-noncommSkewConn) = 0 := by
    ext x y i
    dsimp [meanConn]
    simp
  have hSkew : skewConnTensor noncommSkewConn (-noncommSkewConn) = noncommSkewConn := by
    ext x y i
    dsimp [skewConnTensor]
    exact scalar_half_sub_neg _
  have hRzero :
      connCurvature (0 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
        (meanConn noncommSkewConn (-noncommSkewConn)) e0 e1 = 0 := by
    rw [hMean]
    ext y i
    simp [connCurvature, endComm]
  rw [hRzero, smul_zero, zero_add, hSkew] at hSum
  refine ⟨hSum, ?_⟩
  intro hZero
  have hEval := congrArg (fun f : Module.End ℝ (Fin 2 → ℝ) => f ![1, 0] 0) hZero
  simp [endComm, noncommSkewConn, e0, e1] at hEval

end MilnorOctahedralAndDualCurvatureBridge

/-! ## QMS `TypedArchetype` Certification -/

section QMSCertification

/-- Combined certified `TypedArchetype` uniting Pathways 1, 2, and 4 over noncommutative
Clifford, matrix, and dual-connection carriers. -/
noncomputable def coherenceJKOEguchiMilnorArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.InformationGeometry.CoherenceJKOFlowAndEguchiBridge.coherenceJKOEguchiMilnorArchetype
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (∀ (u₀ u : Cl31) (τ : ℝ), 0 < τ →
      scaledParsimoniousJKO Q31 τ u₀ (jkoGraceResolvent Q31 τ u₀) ≤
        scaledParsimoniousJKO Q31 τ u₀ u ∧
      (scaledParsimoniousJKO Q31 τ u₀ u =
          scaledParsimoniousJKO Q31 τ u₀ (jkoGraceResolvent Q31 τ u₀) ↔
        u = jkoGraceResolvent Q31 τ u₀)) ∧
    jkoGraceResolvent Q31 1 = graceOperator Q31 ∧
    (∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A) ∧
    (∀ {θ : ℝ} {z : ℂ}, θ ≠ 0 → z ≠ 0 →
      (gibbsDensityC θ + Matrix.of ![![0, z], ![star z, 0]]) * gibbsDensityC θ ≠
        gibbsDensityC θ * (gibbsDensityC θ + Matrix.of ![![0, z], ![star z, 0]])) ∧
    (∃ A B : Module.End ℝ (Fin 2 → ℝ), A * B ≠ B * A) ∧
    endComm (noncommSkewConn (Pi.single 0 (1 : ℝ)))
      (noncommSkewConn (Pi.single 1 (1 : ℝ))) ≠ 0
  evidence := fun _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u₀ u τ hτ
      exact jkoGraceResolvent_is_unique_minimizer Q31 hτ u₀ u
    · exact jkoGraceResolvent_unit_step Q31
    · exact mat2c_jko_noncommutative
    · intro θ z hθ hz
      exact quantum_coherent_state_gibbs_noncommutativity hθ hz
    · exact moduleEnd_fin2_noncommutative
    · exact noncommSkewConn_dual_curvature_sum_nonzero.2

#register_archetype coherenceJKOEguchiMilnorArchetype
#audit_archetype coherenceJKOEguchiMilnorArchetype

end QMSCertification

end InfoGeometry.InformationGeometry.CoherenceJKOFlowAndEguchiBridge
