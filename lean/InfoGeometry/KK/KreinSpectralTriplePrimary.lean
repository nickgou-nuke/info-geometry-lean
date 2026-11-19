/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.ClNNFredholmBridge
import InfoGeometry.KK.RealSplitKreinEquivarianceBridge
import InfoGeometry.KK.SpectralTripleKreinCycleBridge
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.Canonical.BulkBoundaryTomitaTransportBridge
import InfoGeometry.Canonical.CantorKMSFiniteTomitaBridge
import InfoGeometry.Clifford.TomitaInversionBridge
import InfoGeometry.SuperMetriplectic.SouriauTomitaBKM
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Primary-Source Krein Spectral Triple & Modular Foundations (`S3-23`..`S3-28`)

Primary-source formalization for Pillar 4 (`R2 / M3.2–M3.5`):

* `S3-23` — Tomita–Takesaki (1970): commutant subalgebra, real-linear Tomita map `S = J Δ^{1/2}`,
  modular conjugation `J` vs modular operator `Δ`, fundamental inclusion `J M J ⊆ M'`, modular
  automorphism group `σ_t`, concrete noncommutative `M₂(ℂ)` Tomita witness with `Δ ≠ 1`, and
  connections with the repository modular-transport infrastructure
  (`BulkBoundaryTomitaTransportBridge`, `TomitaInversionBridge`, `CantorKMSFiniteTomitaBridge`,
  `SouriauTomitaBKM`) (`R3.1`, `R3.3`).
* `S3-24` — Kasparov (1980): real Clifford algebras `Cl_{p,q}` of signature `(p, q)`, real
  `ℤ₂`-graded Clifford cycles `KasparovRealGradedCliffordCycle`, Koszul supercommutation on the
  real split tower, and stage equivariant Fredholm index preservation (`R3.1`, `R3.3`).
* `S3-25`..`S3-28` — Connes (1995/1996), Paschke–Sitarz (2006), Strohmaier (2006), and
  Van den Dungen–Paschke–Rennie (2013): KO-dimension sign tables, `ε ↔ ε'` convention
  equivalence, skew-adjoint vs self-adjoint fundamental symmetries `β = K J_sym`, Krein
  skew-adjointness vs `β`-self-adjointness, Wick rotation, `PseudoRiemannianKreinTriple`,
  strict separation of `(K, J, β)`, and a concrete `KO = 0` pseudo-Riemannian Krein witness
  (`R3.1`, `R3.3`).
-/

noncomputable section

namespace InfoGeometry.KK.KreinSpectralTriplePrimary

open scoped InnerProductSpace GradedTensorProduct
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.SpectralTriple

/-! ## Part 1 (`S3-23`): Tomita–Takesaki Modular Theory & Real Flow Equivalence -/

section TomitaTakesaki

/--
Commutant subalgebra `M'` of a complex bounded-operator subalgebra `M ⊆ B(H)` (`S3-23`,
Takesaki 1970, Ch. I; `R3.1`).
-/
def commutantSubalgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : Subalgebra ℂ (H →L[ℂ] H)) : Subalgebra ℂ (H →L[ℂ] H) where
  carrier := {T : H →L[ℂ] H | ∀ a ∈ M, T.comp a = a.comp T}
  mul_mem' := by
    intro S T hS hT a ha
    change (S.comp T).comp a = a.comp (S.comp T)
    rw [ContinuousLinearMap.comp_assoc, hT a ha, ← ContinuousLinearMap.comp_assoc, hS a ha,
      ContinuousLinearMap.comp_assoc]
  one_mem' := by
    intro a _
    rfl
  add_mem' := by
    intro S T hS hT a ha
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hS a ha, hT a ha]
  zero_mem' := by
    intro a _
    simp
  algebraMap_mem' := by
    intro c a _
    change (c • ContinuousLinearMap.id ℂ H).comp a = a.comp (c • ContinuousLinearMap.id ℂ H)
    simp

/--
Membership characterization for the commutant subalgebra `M'` (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem mem_commutantSubalgebra_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : Subalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ commutantSubalgebra M ↔ ∀ a ∈ M, T.comp a = a.comp T :=
  Iff.rfl

/--
Every subalgebra `M ⊆ B(H)` sits inside its bicommutant `M''` (`S3-23`, von Neumann / Takesaki
1970; `R3.1`).
-/
theorem le_bicommutant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : Subalgebra ℂ (H →L[ℂ] H)) :
    M ≤ commutantSubalgebra (commutantSubalgebra M) := by
  intro a ha T hT
  exact (hT a ha).symm

/--
Algebraic Tomita–Takesaki modular system on a complex Hilbert space `H` (`S3-23`, Tomita 1967 /
Takesaki 1970, Thm. 1; `R3.1`, `R3.3`): keeps the conjugate-linear Tomita involution `S_op`,
conjugate-linear antiunitary modular conjugation `J_mod`, strictly positive self-adjoint modular
square root `Δ^{1/2}`, polar decomposition `S_op = J_mod ∘ Δ^{1/2}`, and fundamental inclusion
`J_mod M J_mod ⊆ M'`.
-/
structure AlgebraicTomitaModularSystem
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  alg : Subalgebra ℂ (H →L[ℂ] H)
  alg_star : ∀ a ∈ alg, ContinuousLinearMap.adjoint a ∈ alg
  S_op : H →ₗ[ℝ] H
  S_antilinear : ∀ (c : ℂ) (x : H), S_op (c • x) = (star c) • S_op x
  S_involutive : ∀ x : H, S_op (S_op x) = x
  J_mod : H →ₗ[ℝ] H
  J_mod_antilinear : ∀ (c : ℂ) (x : H), J_mod (c • x) = (star c) • J_mod x
  J_mod_involutive : ∀ x : H, J_mod (J_mod x) = x
  J_mod_antiunitary : ∀ x y : H, ⟪J_mod x, J_mod y⟫_ℂ = star ⟪x, y⟫_ℂ
  deltaHalf : H →L[ℂ] H
  deltaHalf_selfAdjoint : ContinuousLinearMap.adjoint deltaHalf = deltaHalf
  deltaHalf_pos : ∀ x : H, x ≠ 0 → 0 < (⟪deltaHalf x, x⟫_ℂ).re
  deltaHalf_invertible : IsUnit deltaHalf
  polar_decomposition : ∀ x : H, S_op x = J_mod (deltaHalf x)
  J_mod_deltaHalf_inversion : ∀ x : H, J_mod (deltaHalf (J_mod (deltaHalf x))) = x
  tomita_fundamental_inclusion :
    ∀ a ∈ alg, ∃ a' ∈ commutantSubalgebra alg, ∀ x : H, J_mod (a (J_mod x)) = a' x

namespace AlgebraicTomitaModularSystem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Modular conjugation `J_mod` is isometric on `H` (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem J_mod_norm_eq (sys : AlgebraicTomitaModularSystem H) (x : H) :
    ‖sys.J_mod x‖ = ‖x‖ := by
  have hsq : ‖sys.J_mod x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      sys.J_mod_antiunitary x x]
    simp only [RCLike.re_to_complex, RCLike.star_def, Complex.conj_re]
  nlinarith [norm_nonneg (sys.J_mod x), norm_nonneg x]

/--
Modular operator `Δ = (Δ^{1/2})^2` (`S3-23`, Takesaki 1970; `R3.1`).
-/
def delta (sys : AlgebraicTomitaModularSystem H) : H →L[ℂ] H :=
  sys.deltaHalf.comp sys.deltaHalf

/--
`Δ = (Δ^{1/2})^2` is Hilbert self-adjoint (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem delta_selfAdjoint (sys : AlgebraicTomitaModularSystem H) :
    ContinuousLinearMap.adjoint sys.delta = sys.delta := by
  unfold delta
  rw [ContinuousLinearMap.adjoint_comp, sys.deltaHalf_selfAdjoint]

/--
`Δ = (Δ^{1/2})^2` has strictly positive inner product on nonzero vectors (`S3-23`,
Takesaki 1970; `R3.1`).
-/
theorem delta_pos_inner (sys : AlgebraicTomitaModularSystem H) (x : H) (hx : x ≠ 0) :
    0 < (⟪sys.delta x, x⟫_ℂ).re := by
  have hdx0 : sys.deltaHalf x ≠ 0 := by
    intro h0
    rcases sys.deltaHalf_invertible with ⟨u, hu⟩
    have h1 : (↑u⁻¹ : H →L[ℂ] H) (sys.deltaHalf x) = x := by
      have hcomp := congrArg (fun T : H →L[ℂ] H => T x) (show (↑u⁻¹ : H →L[ℂ] H).comp sys.deltaHalf =
        ContinuousLinearMap.id ℂ H by
          rw [← hu]
          exact Units.inv_mul u)
      simpa using hcomp
    rw [h0, map_zero] at h1
    exact hx h1.symm
  have hinner : ⟪sys.delta x, x⟫_ℂ = ⟪sys.deltaHalf x, sys.deltaHalf x⟫_ℂ := by
    calc
      ⟪sys.deltaHalf (sys.deltaHalf x), x⟫_ℂ =
          ⟪sys.deltaHalf x, ContinuousLinearMap.adjoint sys.deltaHalf x⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪sys.deltaHalf x, sys.deltaHalf x⟫_ℂ := by rw [sys.deltaHalf_selfAdjoint]
  rw [hinner]
  change 0 < RCLike.re ⟪sys.deltaHalf x, sys.deltaHalf x⟫_ℂ
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact sq_pos_of_pos (norm_pos_iff.mpr hdx0)

/--
`Δ = (Δ^{1/2})^2` is invertible in `B(H)` (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem delta_invertible (sys : AlgebraicTomitaModularSystem H) : IsUnit sys.delta :=
  sys.deltaHalf_invertible.mul sys.deltaHalf_invertible

/--
Tomita modular inversion identity `J Δ J Δ = 1`, i.e., `J Δ J = Δ⁻¹` (`S3-23`,
Takesaki 1970, Lem. 1.1; `R3.1`).
-/
theorem J_mod_delta_inversion (sys : AlgebraicTomitaModularSystem H) (x : H) :
    sys.J_mod (sys.delta (sys.J_mod (sys.delta x))) = x := by
  have h1 : sys.J_mod (sys.deltaHalf (sys.J_mod (sys.deltaHalf (sys.deltaHalf x)))) =
      sys.deltaHalf x := sys.J_mod_deltaHalf_inversion (sys.deltaHalf x)
  have h2 : sys.deltaHalf (sys.J_mod (sys.deltaHalf (sys.deltaHalf x))) =
      sys.J_mod (sys.deltaHalf x) := by
    have := congrArg sys.J_mod h1
    rwa [sys.J_mod_involutive] at this
  have h3 : sys.J_mod (sys.delta (sys.J_mod (sys.delta x))) =
      sys.J_mod (sys.deltaHalf (sys.J_mod (sys.deltaHalf x))) := by
    change sys.J_mod (sys.deltaHalf (sys.deltaHalf (sys.J_mod (sys.deltaHalf (sys.deltaHalf x))))) = _
    rw [h2]
  rw [h3]
  exact sys.J_mod_deltaHalf_inversion x

/--
Complex-linear conjugation `a ↦ J_mod ∘ a ∘ J_mod` on bounded operators (`S3-23`, Takesaki 1970;
`R3.1`). Since `J_mod` is conjugate-linear and isometric, `J_mod ∘ a ∘ J_mod` is `ℂ`-linear and
bounded with operator norm at most `‖a‖`.
-/
def modularConjugate (sys : AlgebraicTomitaModularSystem H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => sys.J_mod (a (sys.J_mod x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        simp [sys.J_mod_antilinear, map_smul] }
    ‖a‖
    (fun x => by
      change ‖sys.J_mod (a (sys.J_mod x))‖ ≤ ‖a‖ * ‖x‖
      rw [sys.J_mod_norm_eq]
      calc
        ‖a (sys.J_mod x)‖ ≤ ‖a‖ * ‖sys.J_mod x‖ := a.le_opNorm _
        _ = ‖a‖ * ‖x‖ := by rw [sys.J_mod_norm_eq])

/--
Application formula for `modularConjugate` (`S3-23`, Takesaki 1970; `R3.1`).
-/
@[simp]
theorem modularConjugate_apply (sys : AlgebraicTomitaModularSystem H) (a : H →L[ℂ] H) (x : H) :
    sys.modularConjugate a x = sys.J_mod (a (sys.J_mod x)) := by
  dsimp only [modularConjugate]
  rfl

/--
`modularConjugate` is an involution on `B(H)` (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem modularConjugate_involutive (sys : AlgebraicTomitaModularSystem H) (a : H →L[ℂ] H) :
    sys.modularConjugate (sys.modularConjugate a) = a := by
  ext x
  simp [sys.J_mod_involutive]

/--
`modularConjugate` preserves operator composition (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem modularConjugate_comp (sys : AlgebraicTomitaModularSystem H) (a b : H →L[ℂ] H) :
    sys.modularConjugate (a.comp b) = (sys.modularConjugate a).comp (sys.modularConjugate b) := by
  ext x
  simp [sys.J_mod_involutive]

/--
Fundamental Tomita inclusion in `B(H)`: `a ∈ M → modularConjugate sys a ∈ M'` (`S3-23`,
Tomita–Takesaki 1970, Thm. 1; `R3.1`).
-/
theorem modularConjugate_mem_commutant (sys : AlgebraicTomitaModularSystem H)
    {a : H →L[ℂ] H} (ha : a ∈ sys.alg) :
    sys.modularConjugate a ∈ commutantSubalgebra sys.alg := by
  rcases sys.tomita_fundamental_inclusion a ha with ⟨a', ha', heq⟩
  have hEq : sys.modularConjugate a = a' := by
    ext x
    exact heq x
  simpa [hEq] using ha'

/--
Tomita–Takesaki equality `modularConjugate sys '' alg = commutantSubalgebra alg` whenever
`alg` satisfies `alg'' = alg` and `J_mod M' J_mod ⊆ M''` (`S3-23`, Takesaki 1970, Thm. 1; `R3.1`).
-/
theorem modularConjugate_image_eq_commutant
    (sys : AlgebraicTomitaModularSystem H)
    (hCommConj : ∀ b ∈ commutantSubalgebra sys.alg,
      sys.modularConjugate b ∈ commutantSubalgebra (commutantSubalgebra sys.alg))
    (hBicommutant : commutantSubalgebra (commutantSubalgebra sys.alg) = sys.alg) :
    sys.modularConjugate '' (sys.alg : Set (H →L[ℂ] H)) =
      (commutantSubalgebra sys.alg : Set (H →L[ℂ] H)) := by
  ext T
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact sys.modularConjugate_mem_commutant ha
  · intro hT
    have hconj : sys.modularConjugate T ∈ sys.alg := by
      rw [← hBicommutant]
      exact hCommConj T hT
    exact ⟨sys.modularConjugate T, hconj, sys.modularConjugate_involutive T⟩

end AlgebraicTomitaModularSystem

/--
Complex modular automorphism flow `σ_t(a) = exp(-i t K) ∘ a ∘ exp(i t K)` generated by a
modular Hamiltonian `K_log` (`S3-23`, Takesaki 1970; `R3.1`).
-/
def complexModularFlow
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K_log : H →L[ℂ] H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  (NormedSpace.exp ((-Complex.I * (t : ℂ)) • K_log)).comp
    (a.comp (NormedSpace.exp ((Complex.I * (t : ℂ)) • K_log)))

/--
Group composition law `σ_s(σ_t(a)) = σ_{s+t}(a)` for the complex modular automorphism flow
(`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem complexModularFlow_add
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K_log : H →L[ℂ] H) (s t : ℝ) (a : H →L[ℂ] H) :
    complexModularFlow K_log s (complexModularFlow K_log t a) =
      complexModularFlow K_log (s + t) a := by
  unfold complexModularFlow
  have hcommL : Commute ((-Complex.I * (s : ℂ)) • K_log) ((-Complex.I * (t : ℂ)) • K_log) :=
    (Commute.refl K_log).smul_left _ |>.smul_right _
  have hcommR : Commute ((Complex.I * (t : ℂ)) • K_log) ((Complex.I * (s : ℂ)) • K_log) :=
    (Commute.refl K_log).smul_left _ |>.smul_right _
  have hL :
      (NormedSpace.exp ((-Complex.I * (s : ℂ)) • K_log)).comp
          (NormedSpace.exp ((-Complex.I * (t : ℂ)) • K_log)) =
        NormedSpace.exp ((-Complex.I * ((s + t : ℝ) : ℂ)) • K_log) := by
    rw [← ContinuousLinearMap.mul_def,
      ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcommL
        ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)]
    congr 1
    rw [← add_smul, Complex.ofReal_add]
    congr 1
    ring
  have hR :
      (NormedSpace.exp ((Complex.I * (t : ℂ)) • K_log)).comp
          (NormedSpace.exp ((Complex.I * (s : ℂ)) • K_log)) =
        NormedSpace.exp ((Complex.I * ((s + t : ℝ) : ℂ)) • K_log) := by
    rw [← ContinuousLinearMap.mul_def,
      ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcommR
        ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)]
    congr 1
    rw [← add_smul, Complex.ofReal_add]
    congr 1
    ring
  simp only [← ContinuousLinearMap.mul_def] at hL hR ⊢
  simp only [mul_assoc]
  rw [hR, ← mul_assoc (NormedSpace.exp ((-Complex.I * (s : ℂ)) • K_log)), hL]

/--
Modular conjugation `J_mod` commutes with the complex modular flow when `J_mod ∘ K_log = -K_log ∘ J_mod`
(`S3-23`, Takesaki 1970, Thm. 1; `R3.1`).
-/
theorem J_mod_intertwines_complexModularFlow
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sys : AlgebraicTomitaModularSystem H)
    (K_log : H →L[ℂ] H)
    (hJK : ∀ x : H, sys.J_mod (K_log x) = -(K_log (sys.J_mod x)))
    (t : ℝ) (a : H →L[ℂ] H) :
    sys.modularConjugate (complexModularFlow K_log t a) =
      complexModularFlow K_log t (sys.modularConjugate a) := by
  have hPowL : ∀ (c : ℂ) (k : ℕ) (x : H),
      sys.J_mod (((c • K_log) ^ k) x) = (((-(star c)) • K_log) ^ k) (sys.J_mod x) := by
    intro c k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        FunLike.coe_smul, Pi.smul_apply, sys.J_mod_antilinear, hJK, smul_neg, ih x,
        ← neg_smul, ← Pi.smul_apply, ← FunLike.coe_smul, ← ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.mul_def, ← pow_succ']
  have hExp : ∀ (c : ℂ) (x : H),
      sys.J_mod (NormedSpace.exp (c • K_log) x) =
        NormedSpace.exp ((-(star c)) • K_log) (sys.J_mod x) := by
    intro c x
    rw [NormedSpace.exp_eq_tsum ℂ]
    have hBall1 : (c • K_log) ∈ Metric.eball (0 : H →L[ℂ] H) (NormedSpace.expSeries ℂ (H →L[ℂ] H)).radius := by
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _
    have hBall2 : ((-(star c)) • K_log) ∈
        Metric.eball (0 : H →L[ℂ] H) (NormedSpace.expSeries ℂ (H →L[ℂ] H)).radius := by
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _
    have hSumm1 : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • (c • K_log) ^ k) :=
      NormedSpace.expSeries_summable_of_mem_ball' (𝕂 := ℂ) (c • K_log) hBall1
    have hSumm2 : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • ((-(star c)) • K_log) ^ k) :=
      NormedSpace.expSeries_summable_of_mem_ball' (𝕂 := ℂ) ((-(star c)) • K_log) hBall2
    have hsum1 : Summable (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹ • (c • K_log) ^ k) x) :=
      hSumm1.map (ContinuousLinearMap.apply ℂ H x).toAddMonoidHom
        (ContinuousLinearMap.apply ℂ H x).continuous
    have htsum1 : (∑' k : ℕ, (Nat.factorial k : ℂ)⁻¹ • (c • K_log) ^ k) x =
        ∑' k : ℕ, ((Nat.factorial k : ℂ)⁻¹ • (c • K_log) ^ k) x :=
      (ContinuousLinearMap.apply ℂ H x).map_tsum hSumm1
    have htsum2 : (∑' k : ℕ, (Nat.factorial k : ℂ)⁻¹ • ((-(star c)) • K_log) ^ k) (sys.J_mod x) =
        ∑' k : ℕ, ((Nat.factorial k : ℂ)⁻¹ • ((-(star c)) • K_log) ^ k) (sys.J_mod x) :=
      (ContinuousLinearMap.apply ℂ H (sys.J_mod x)).map_tsum hSumm2
    let Jclm : H →L[ℝ] H := sys.J_mod.mkContinuous 1 fun u => by
      rw [one_mul, sys.J_mod_norm_eq]
    have hmap : sys.J_mod (∑' k : ℕ, ((Nat.factorial k : ℂ)⁻¹ • (c • K_log) ^ k) x) =
        ∑' k : ℕ, sys.J_mod (((Nat.factorial k : ℂ)⁻¹ • (c • K_log) ^ k) x) :=
      Jclm.map_tsum hsum1
    rw [htsum1, htsum2, hmap]
    refine tsum_congr fun k => ?_
    rw [FunLike.coe_smul, Pi.smul_apply, sys.J_mod_antilinear,
      star_inv₀, star_natCast, hPowL, ← Pi.smul_apply, ← FunLike.coe_smul]
  have hstarL : -(star (-Complex.I * (t : ℂ))) = -Complex.I * (t : ℂ) := by
    simp [Complex.conj_ofReal]
  have hstarR : -(star (Complex.I * (t : ℂ))) = Complex.I * (t : ℂ) := by
    simp [Complex.conj_ofReal]
  ext x
  simp only [AlgebraicTomitaModularSystem.modularConjugate_apply, complexModularFlow,
    ContinuousLinearMap.comp_apply]
  rw [hExp (-Complex.I * (t : ℂ)), hstarL]
  congr 1
  have hExpR : NormedSpace.exp ((Complex.I * (t : ℂ)) • K_log) (sys.J_mod x) =
      sys.J_mod (NormedSpace.exp ((Complex.I * (t : ℂ)) • K_log) x) := by
    have hE := hExp (Complex.I * (t : ℂ)) x
    rw [hstarR] at hE
    exact hE.symm
  rw [hExpR]

/-! ### Concrete Noncommutative `M₂(ℂ)` Tomita–Takesaki Witness & T16 Witnesses -/

/--
Hilbert–Schmidt GNS carrier `ℂ^{2 × 2}` (`EuclideanSpace ℂ (Fin 2 × Fin 2)`) for the concrete
noncommutative `M₂(ℂ)` Tomita–Takesaki witness (`S3-23`, Takesaki 1970; `R3.1`).
-/
abbrev Mat2Hilbert := EuclideanSpace ℂ (Fin 2 × Fin 2)

/--
Convert a `2 × 2` complex matrix to `Mat2Hilbert` (`S3-23`; `R3.1`).
-/
def mat2ToHilbert (X : Matrix (Fin 2) (Fin 2) ℂ) : Mat2Hilbert :=
  WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => X p.1 p.2)

/--
Convert a vector in `Mat2Hilbert` back to a `2 × 2` complex matrix (`S3-23`; `R3.1`).
-/
def hilbertToMat2 (X : Mat2Hilbert) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of (fun i j => X (i, j))

private lemma hilbertToMat2_mat2ToHilbert (M : Matrix (Fin 2) (Fin 2) ℂ) :
    hilbertToMat2 (mat2ToHilbert M) = M := by
  ext i j
  rfl

/--
Closed T16 non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ` (`S3-23`; `R3.1`).
-/
theorem matrix2C_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  refine ⟨A, B, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h00

/--
Left multiplication continuous linear operator `L_A(X) = A * X` on `Mat2Hilbert` (`S3-23`,
Takesaki 1970; `R3.1`).
-/
def mat2LeftMulCLM (A : Matrix (Fin 2) (Fin 2) ℂ) : Mat2Hilbert →L[ℂ] Mat2Hilbert :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => mat2ToHilbert (A * hilbertToMat2 X)
      map_add' := fun X Y => by
        ext ⟨i, j⟩
        have hadd : hilbertToMat2 (X + Y) = hilbertToMat2 X + hilbertToMat2 Y := rfl
        simp only [mat2ToHilbert, PiLp.toLp_apply, hadd, Matrix.mul_add, Matrix.add_apply,
          PiLp.add_apply]
      map_smul' := fun c X => by
        ext ⟨i, j⟩
        have hsmul : hilbertToMat2 (c • X) = c • hilbertToMat2 X := rfl
        simp only [RingHom.id_apply, mat2ToHilbert, PiLp.toLp_apply, hsmul, Matrix.mul_smul,
          Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply] }

private lemma mat2LeftMulCLM_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (X : Mat2Hilbert) :
    mat2LeftMulCLM A X = mat2ToHilbert (A * hilbertToMat2 X) := rfl

/--
Right multiplication continuous linear operator `R_B(X) = X * B` on `Mat2Hilbert` (`S3-23`,
Takesaki 1970; `R3.1`).
-/
def mat2RightMulCLM (B : Matrix (Fin 2) (Fin 2) ℂ) : Mat2Hilbert →L[ℂ] Mat2Hilbert :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => mat2ToHilbert (hilbertToMat2 X * B)
      map_add' := fun X Y => by
        ext ⟨i, j⟩
        have hadd : hilbertToMat2 (X + Y) = hilbertToMat2 X + hilbertToMat2 Y := rfl
        simp only [mat2ToHilbert, PiLp.toLp_apply, hadd, Matrix.add_mul, Matrix.add_apply,
          PiLp.add_apply]
      map_smul' := fun c X => by
        ext ⟨i, j⟩
        have hsmul : hilbertToMat2 (c • X) = c • hilbertToMat2 X := rfl
        simp only [RingHom.id_apply, mat2ToHilbert, PiLp.toLp_apply, hsmul, Matrix.smul_mul,
          Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply] }

private lemma mat2RightMulCLM_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (X : Mat2Hilbert) :
    mat2RightMulCLM B X = mat2ToHilbert (hilbertToMat2 X * B) := rfl

/--
Closed T16 non-commutativity witness for `Mat2Hilbert →L[ℂ] Mat2Hilbert` (`S3-23`; `R3.1`).
-/
theorem mat2Hilbert_end_noncomm :
    ∃ A B : Mat2Hilbert →L[ℂ] Mat2Hilbert, A.comp B ≠ B.comp A := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  refine ⟨mat2LeftMulCLM A, mat2LeftMulCLM B, fun h => ?_⟩
  have h1 := congrArg (fun T : Mat2Hilbert →L[ℂ] Mat2Hilbert =>
    (T (mat2ToHilbert 1)) (0, 0)) h
  norm_num [mat2LeftMulCLM_apply, mat2ToHilbert, hilbertToMat2, A, B, Matrix.mul_apply,
    Fin.sum_univ_two] at h1

/--
Left multiplication subalgebra `L(M₂(ℂ)) ⊆ B(Mat2Hilbert)` (`S3-23`, Takesaki 1970; `R3.1`).
-/
def mat2LeftAlgebra : Subalgebra ℂ (Mat2Hilbert →L[ℂ] Mat2Hilbert) where
  carrier := Set.range mat2LeftMulCLM
  mul_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    refine ⟨A * B, ?_⟩
    ext X ⟨i, j⟩
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      mat2LeftMulCLM_apply, mat2ToHilbert, hilbertToMat2, PiLp.toLp_apply, Matrix.mul_assoc]
    rfl
  one_mem' := by
    refine ⟨1, ?_⟩
    ext X ⟨i, j⟩
    simp only [mat2LeftMulCLM_apply, mat2ToHilbert, PiLp.toLp_apply, Matrix.one_mul]
    rfl
  add_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    refine ⟨A + B, ?_⟩
    ext X ⟨i, j⟩
    simp only [mat2LeftMulCLM_apply, mat2ToHilbert, PiLp.toLp_apply, add_apply,
      PiLp.add_apply, Matrix.add_mul, Matrix.add_apply]
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext X ⟨i, j⟩
    simp only [mat2LeftMulCLM_apply, mat2ToHilbert, PiLp.toLp_apply, Matrix.zero_mul,
      zero_apply, PiLp.zero_apply, Matrix.zero_apply]
  algebraMap_mem' := fun c => by
    refine ⟨c • (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
    ext X ⟨i, j⟩
    simp only [mat2LeftMulCLM_apply, mat2ToHilbert, PiLp.toLp_apply,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul,
      smul_apply, PiLp.smul_apply, smul_eq_mul]
    rfl

private def mat2Weight (i : Fin 2) : ℝ := if i = 0 then 2 else 1

private def mat2DeltaHalfCLM : Mat2Hilbert →L[ℂ] Mat2Hilbert :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => WithLp.toLp 2 (fun p : Fin 2 × Fin 2 =>
        ((mat2Weight p.1 / mat2Weight p.2 : ℝ) : ℂ) * X p)
      map_add' := fun X Y => by
        ext ⟨i, j⟩
        simp [mul_add]
      map_smul' := fun c X => by
        ext ⟨i, j⟩
        simp [mul_left_comm] }

private lemma mat2DeltaHalfCLM_apply (X : Mat2Hilbert) :
    mat2DeltaHalfCLM X = WithLp.toLp 2 (fun p : Fin 2 × Fin 2 =>
      ((mat2Weight p.1 / mat2Weight p.2 : ℝ) : ℂ) * X p) := rfl

private def mat2DeltaHalfInvCLM : Mat2Hilbert →L[ℂ] Mat2Hilbert :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => WithLp.toLp 2 (fun p : Fin 2 × Fin 2 =>
        ((mat2Weight p.2 / mat2Weight p.1 : ℝ) : ℂ) * X p)
      map_add' := fun X Y => by
        ext ⟨i, j⟩
        simp [mul_add]
      map_smul' := fun c X => by
        ext ⟨i, j⟩
        simp [mul_left_comm] }

private lemma mat2DeltaHalfInvCLM_apply (X : Mat2Hilbert) :
    mat2DeltaHalfInvCLM X = WithLp.toLp 2 (fun p : Fin 2 × Fin 2 =>
      ((mat2Weight p.2 / mat2Weight p.1 : ℝ) : ℂ) * X p) := rfl

private def mat2JModLM : Mat2Hilbert →ₗ[ℝ] Mat2Hilbert where
  toFun X := WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => star (X (p.2, p.1)))
  map_add' X Y := by
    ext ⟨i, j⟩
    simp
  map_smul' r X := by
    ext ⟨i, j⟩
    simp [Algebra.smul_def]

private def mat2SOpLM : Mat2Hilbert →ₗ[ℝ] Mat2Hilbert :=
  mat2JModLM.comp (mat2DeltaHalfCLM.toLinearMap.restrictScalars ℝ)

/--
Concrete non-tracial (`Δ ≠ 1`), noncommutative `M₂(ℂ)` `AlgebraicTomitaModularSystem` witness
(`S3-23`, Takesaki 1970; `R3.1`; T17 inhabitant). Uses diagonal KMS weights `diag(4, 1)` on the
GNS Hilbert space `Mat2Hilbert`.
-/
def matrix2CTomitaSystem : AlgebraicTomitaModularSystem Mat2Hilbert where
  alg := mat2LeftAlgebra
  alg_star := by
    rintro _ ⟨A, rfl⟩
    refine ⟨A.conjTranspose, ?_⟩
    refine (ContinuousLinearMap.eq_adjoint_iff (mat2LeftMulCLM A.conjTranspose)
      (mat2LeftMulCLM A)).2 fun X Y => ?_
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type]
    have hL : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (Z : Mat2Hilbert) (i j : Fin 2),
        (mat2LeftMulCLM M Z).ofLp (i, j) = ∑ k : Fin 2, M i k * Z.ofLp (k, j) := by
      intro M Z i j
      simp [mat2LeftMulCLM_apply, mat2ToHilbert, hilbertToMat2, Matrix.mul_apply]
    simp_rw [hL, Matrix.conjTranspose_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Fin.sum_univ_two, RCLike.star_def, starRingEnd_self_apply]
    ring
  S_op := mat2SOpLM
  S_antilinear := fun c X => by
    ext ⟨i, j⟩
    simp [mat2SOpLM, mat2JModLM, mat2DeltaHalfCLM_apply, mul_left_comm]
  S_involutive := fun X => by
    ext ⟨i, j⟩
    have hw : ∀ k : Fin 2, mat2Weight k ≠ 0 := by
      intro k
      fin_cases k <;> norm_num [mat2Weight]
    dsimp only [mat2SOpLM, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      ContinuousLinearMap.coe_coe]
    simp only [mat2JModLM, LinearMap.coe_mk, AddHom.coe_mk, mat2DeltaHalfCLM_apply,
      PiLp.toLp_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
    push_cast
    field_simp [hw i, hw j]
  J_mod := mat2JModLM
  J_mod_antilinear := fun c X => by
    ext ⟨i, j⟩
    simp [mat2JModLM]
  J_mod_involutive := fun X => by
    ext ⟨i, j⟩
    simp [mat2JModLM]
  J_mod_antiunitary := fun X Y => by
    simp only [PiLp.inner_apply, RCLike.inner_apply, mat2JModLM, LinearMap.coe_mk, AddHom.coe_mk,
      RCLike.star_def]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type_right]
    simp only [map_sum, map_mul, starRingEnd_self_apply, mul_comm]
  deltaHalf := mat2DeltaHalfCLM
  deltaHalf_selfAdjoint := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff mat2DeltaHalfCLM mat2DeltaHalfCLM).2 fun X Y => ?_
    simp only [PiLp.inner_apply, mat2DeltaHalfCLM_apply]
    simp_rw [RCLike.inner_apply]
    simp only [map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  deltaHalf_pos := fun X hX => by
    have hex : ∃ p : Fin 2 × Fin 2, X p ≠ 0 := by
      by_contra h
      push Not at h
      apply hX
      ext p
      exact h p
    rcases hex with ⟨p₀, hp₀⟩
    have hre : (⟪mat2DeltaHalfCLM X, X⟫_ℂ).re =
        ∑ p : Fin 2 × Fin 2, (mat2Weight p.1 / mat2Weight p.2) * ‖X p‖ ^ 2 := by
      simp only [PiLp.inner_apply, mat2DeltaHalfCLM_apply, Complex.re_sum]
      simp_rw [RCLike.inner_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hsq : (X.ofLp p * (starRingEnd ℂ) (X.ofLp p)).re = ‖X p‖ ^ 2 := by
        have h := norm_sq_eq_re_inner (𝕜 := ℂ) (X p)
        rw [RCLike.re_to_complex, RCLike.inner_apply] at h
        exact h.symm
      calc
        (X.ofLp p * (starRingEnd ℂ)
            (((mat2Weight p.1 / mat2Weight p.2 : ℝ) : ℂ) * X.ofLp p)).re =
            (((mat2Weight p.1 / mat2Weight p.2 : ℝ) : ℂ) *
              (X.ofLp p * (starRingEnd ℂ) (X.ofLp p))).re := by
          simp [map_mul, Complex.conj_ofReal, mul_left_comm]
        _ = (mat2Weight p.1 / mat2Weight p.2) * (X.ofLp p * (starRingEnd ℂ) (X.ofLp p)).re := by
          simp
        _ = (mat2Weight p.1 / mat2Weight p.2) * ‖X p‖ ^ 2 := by rw [hsq]
    rw [hre]
    have hw_pos : ∀ k : Fin 2, 0 < mat2Weight k := fun k => by
      fin_cases k <;> norm_num [mat2Weight]
    refine Finset.sum_pos' (fun p _ => mul_nonneg (div_pos (hw_pos p.1) (hw_pos p.2)).le
      (sq_nonneg _)) ⟨p₀, Finset.mem_univ p₀,
      mul_pos (div_pos (hw_pos p₀.1) (hw_pos p₀.2)) (sq_pos_of_pos (norm_pos_iff.mpr hp₀))⟩
  deltaHalf_invertible := by
    refine ⟨⟨mat2DeltaHalfCLM, mat2DeltaHalfInvCLM, ?_, ?_⟩, rfl⟩
    · ext X ⟨i, j⟩
      have hw : ∀ k : Fin 2, mat2Weight k ≠ 0 := fun k => by fin_cases k <;> norm_num [mat2Weight]
      simp [mat2DeltaHalfCLM_apply, mat2DeltaHalfInvCLM_apply]
      field_simp [hw i, hw j]
    · ext X ⟨i, j⟩
      have hw : ∀ k : Fin 2, mat2Weight k ≠ 0 := fun k => by fin_cases k <;> norm_num [mat2Weight]
      simp [mat2DeltaHalfCLM_apply, mat2DeltaHalfInvCLM_apply]
      field_simp [hw i, hw j]
  polar_decomposition := fun _ => rfl
  J_mod_deltaHalf_inversion := fun X => by
    ext ⟨i, j⟩
    have hw : ∀ k : Fin 2, mat2Weight k ≠ 0 := fun k => by fin_cases k <;> norm_num [mat2Weight]
    simp only [mat2JModLM, LinearMap.coe_mk, AddHom.coe_mk, mat2DeltaHalfCLM_apply,
      PiLp.toLp_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
    push_cast
    field_simp [hw i, hw j]
  tomita_fundamental_inclusion := by
    rintro _ ⟨A, rfl⟩
    refine ⟨mat2RightMulCLM A.conjTranspose, ?_, ?_⟩
    · rintro _ ⟨B, rfl⟩
      ext X ⟨i, j⟩
      simp only [ContinuousLinearMap.comp_apply,
        mat2RightMulCLM_apply, mat2LeftMulCLM_apply, mat2ToHilbert, hilbertToMat2,
        Matrix.mul_apply, Matrix.of_apply, PiLp.toLp_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    · intro X
      ext ⟨i, j⟩
      simp only [mat2JModLM, mat2LeftMulCLM_apply, mat2RightMulCLM_apply, mat2ToHilbert,
        hilbertToMat2, Matrix.of_apply, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
        RCLike.star_def, starRingEnd_self_apply]
      refine Finset.sum_congr rfl fun k _ => mul_comm _ _

/--
Non-traciality witness for `matrix2CTomitaSystem`: its modular operator `Δ` is strictly
non-identity (`S3-23`, Takesaki 1970; `R3.1`).
-/
theorem matrix2CTomitaSystem_delta_ne_one :
    matrix2CTomitaSystem.delta ≠ ContinuousLinearMap.id ℂ Mat2Hilbert := by
  intro h
  let E01 : Mat2Hilbert := WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => if p = (0, 1) then 1 else 0)
  have hval := congrArg (fun T : Mat2Hilbert →L[ℂ] Mat2Hilbert => (T E01) (0, 1)) h
  unfold AlgebraicTomitaModularSystem.delta at hval
  simp only [matrix2CTomitaSystem, ContinuousLinearMap.comp_apply, mat2DeltaHalfCLM_apply,
    PiLp.toLp_apply, ContinuousLinearMap.id_apply, E01, mat2Weight] at hval
  norm_num at hval

/-! ### Connections to Repository Real Tomita Infrastructure (`S3-23`, `R3.3`) -/

/--
Bulk-boundary Tomita transport conjugacy (`S3-23`, `R3.3`): forwards
`BulkBoundaryTomitaTransportBridge.transportedOperator_eq_flow_conjugate`.
-/
theorem bulkBoundary_tomita_flow_conjugacy
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : InfoGeometry.Canonical.BulkBoundaryTomitaTransportBridge.ModularBulkBoundaryBridge (E := E))
    (t : ℝ) :
    B.transportedOperator t =
      (B.logData.flow t).comp (B.ownedOperator.comp (B.logData.flow (-t))) :=
  B.transportedOperator_eq_flow_conjugate t

/--
Clifford conformal inversion as Tomita modular conjugation (`S3-23`, `R3.3`): records
intertwining of left and right Clifford actions by conformal inversion.
-/
theorem clifford_conformalInversion_commutes
    {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V)
    {v0 : V} (hv0_norm : Q v0 = 1) (A X : InfoGeometry.Clifford.Hestenes.ClPlus Q) :
    InfoGeometry.Clifford.TomitaInversionBridge.ConformalInversion Q v0
        (InfoGeometry.Clifford.Hestenes.L_action Q A
          (InfoGeometry.Clifford.TomitaInversionBridge.ConformalInversion Q v0 X)) =
      InfoGeometry.Clifford.Hestenes.R_action Q
        (InfoGeometry.Clifford.TomitaInversionBridge.ConformalInversion Q v0 A) X :=
  InfoGeometry.Clifford.TomitaInversionBridge.conformalInversion_commutes_actions Q v0 hv0_norm A X

/--
Cantor-KMS finite modular complement invariance (`S3-23`, `R3.3`): forwards
`DiagTrace_state_complement_invariant`.
-/
theorem cantorKMS_complement_invariance
    (n : ℕ) (f : InfoGeometry.Canonical.UHFInductiveColimitBoundary.DiagAlg n) :
    (InfoGeometry.Canonical.CantorKMSState.DiagTrace_state n).val
        (InfoGeometry.Canonical.CantorKMSFiniteTomitaBridge.complementPullback f) =
      (InfoGeometry.Canonical.CantorKMSState.DiagTrace_state n).val f :=
  InfoGeometry.Canonical.CantorKMSFiniteTomitaBridge.DiagTrace_state_complement_invariant n f

/--
Souriau–Tomita thermal-time equivalence (`S3-23`, `R3.3`): forwards
`SouriauTomitaThermalTimeCapstone.thermal_time_generator_theorem`.
-/
theorem souriau_tomita_thermal_time_equiv
    {Op : Type*} (C : InfoGeometry.SuperMetriplectic.SouriauTomitaThermalTimeCapstone Op)
    (t : ℝ) (A B : Op) :
    C.derivation.souriauLieDerivation A = C.derivation.thermalTimeDerivation A ∧
      C.thermalTime.souriauThermalFlow t A = C.thermalTime.thermalTimeFlow t A ∧
      C.gravityGradient.relativeEntropyGradientFlow A B =
        C.gravityGradient.spinTwoFierzChannel A B :=
  C.thermal_time_generator_theorem t A B

end TomitaTakesaki

/-! ## Part 2 (`S3-24`): Kasparov (1980) Graded Clifford Cycles -/

section KasparovClifford

open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.KK.RealSplitKreinEquivarianceBridge

/--
Signature weight vector `(1, ..., 1, -1, ..., -1)` of signature `(p, q)` (`S3-24`, Kasparov 1980;
`R3.1`).
-/
def signatureVec (p q : ℕ) : Fin (p + q) → ℝ :=
  fun i => if i.1 < p then 1 else -1

/--
Real quadratic form `∑_{i < p} x_i^2 - ∑_{j < q} x_{p+j}^2` of signature `(p, q)` (`S3-24`,
Kasparov 1980, §2; `R3.1`).
-/
def signatureQForm (p q : ℕ) : QuadraticForm ℝ (Fin (p + q) → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (signatureVec p q)

/--
Real Clifford algebra `Cl_{p,q}` associated to `signatureQForm p q` (`S3-24`, Kasparov 1980, §2;
`R3.1`).
-/
abbrev Clpq (p q : ℕ) : Type := CliffordAlgebra (signatureQForm p q)

/--
Closed T16 non-commutativity witness for `Clpq 1 1` (`S3-24`, Kasparov 1980; `R3.1`).
-/
theorem clpq11_noncomm : ∃ x y : Clpq 1 1, x * y ≠ y * x := by
  let e0 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let e1 : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0
  let f : (Fin 2 → ℝ) →ₗ[ℝ] EndR (DoubledSpace ℝ) :=
    { toFun := fun v => v 0 • KreinSpace.jCLM (H := DoubledSpace ℝ) +
        v 1 • complex_i (E := ℝ)
      map_add' := fun u v => by
        dsimp only [Pi.add_apply]
        module
      map_smul' := fun r u => by
        simp [smul_smul, smul_add] }
  have hf_cond : ∀ v : Fin 2 → ℝ,
      f v * f v = algebraMap ℝ (EndR (DoubledSpace ℝ)) (signatureQForm 1 1 v) := by
    intro v
    have hj_sq : KreinSpace.jCLM (H := DoubledSpace ℝ) *
        KreinSpace.jCLM (H := DoubledSpace ℝ) = 1 := by
      rw [jCLM_eq_spectral_epsilon]
      apply ContinuousLinearMap.ext
      intro u
      apply DoubledSpace.ext <;> simp
    have hi_sq : complex_i (E := ℝ) * complex_i (E := ℝ) = -1 := by
      apply ContinuousLinearMap.ext
      intro u
      apply DoubledSpace.ext <;> simp [complex_i_apply]
    have hij : KreinSpace.jCLM (H := DoubledSpace ℝ) * complex_i (E := ℝ) +
        complex_i (E := ℝ) * KreinSpace.jCLM (H := DoubledSpace ℝ) = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      apply DoubledSpace.ext <;>
        simp [jCLM_eq_spectral_epsilon, spectral_epsilon_apply, complex_i_apply]
    have hq : signatureQForm 1 1 v = v 0 * v 0 - v 1 * v 1 := by
      simp [signatureQForm, signatureVec, QuadraticMap.weightedSumSquares_apply,
        Fin.sum_univ_two]
      ring
    rw [hq]
    change (v 0 • KreinSpace.jCLM (H := DoubledSpace ℝ) + v 1 • complex_i (E := ℝ)) *
        (v 0 • KreinSpace.jCLM (H := DoubledSpace ℝ) + v 1 • complex_i (E := ℝ)) =
      (v 0 * v 0 - v 1 * v 1) • (1 : EndR (DoubledSpace ℝ))
    calc
      (v 0 • KreinSpace.jCLM (H := DoubledSpace ℝ) + v 1 • complex_i (E := ℝ)) *
          (v 0 • KreinSpace.jCLM (H := DoubledSpace ℝ) + v 1 • complex_i (E := ℝ)) =
          (v 0 * v 0) • (KreinSpace.jCLM (H := DoubledSpace ℝ) *
            KreinSpace.jCLM (H := DoubledSpace ℝ)) +
          (v 0 * v 1) • (KreinSpace.jCLM (H := DoubledSpace ℝ) * complex_i (E := ℝ) +
            complex_i (E := ℝ) * KreinSpace.jCLM (H := DoubledSpace ℝ)) +
          (v 1 * v 1) • (complex_i (E := ℝ) * complex_i (E := ℝ)) := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
        rw [mul_comm (v 1) (v 0)]
        abel
      _ = (v 0 * v 0 - v 1 * v 1) • (1 : EndR (DoubledSpace ℝ)) := by
        rw [hj_sq, hij, hi_sq, smul_zero, add_zero, smul_neg, sub_smul, sub_eq_add_neg]
  let liftHom : Clpq 1 1 →ₐ[ℝ] EndR (DoubledSpace ℝ) :=
    CliffordAlgebra.lift (signatureQForm 1 1) ⟨f, hf_cond⟩
  refine ⟨CliffordAlgebra.ι (signatureQForm 1 1) e0,
    CliffordAlgebra.ι (signatureQForm 1 1) e1, fun h => ?_⟩
  have himg := congrArg liftHom h
  rw [map_mul, map_mul, CliffordAlgebra.lift_ι_apply, CliffordAlgebra.lift_ι_apply] at himg
  have h01 : f e0 = KreinSpace.jCLM (H := DoubledSpace ℝ) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [f, e0, jCLM_eq_spectral_epsilon, spectral_epsilon_apply]
  have h10 : f e1 = complex_i (E := ℝ) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [f, e1, complex_i_apply]
  rw [h01, h10] at himg
  have hval := congrArg (fun T : EndR (DoubledSpace ℝ) =>
    WithLp.snd (T (to_doubled (1 : ℝ) (0 : ℝ)))) himg
  norm_num [ContinuousLinearMap.mul_def, jCLM_eq_spectral_epsilon, spectral_epsilon_apply,
    complex_i_apply] at hval

/--
Kasparov (1980) real `ℤ₂`-graded `Cl_{p,q}`-linear Krein Kasparov cycle (`S3-24`, Kasparov 1980,
Def. 1–2; `R3.1`, `R3.3`). Packages an underlying `RealSplitKreinKasparovCycle A B H` together with
odd, Krein `(±)`-adjoint Clifford generators of signature `(p, q)` commuting with both `π(A)` and
`ρ(B)`.
-/
structure KasparovRealGradedCliffordCycle
    (p q : ℕ) (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] where
  base : RealSplitKreinKasparovCycle A B H
  cliffordGens : Fin (p + q) → EndH H
  clifford_odd : ∀ i : Fin (p + q), KreinGradedModule.IsOdd (H := H) (cliffordGens i)
  clifford_sq : ∀ i : Fin (p + q),
    cliffordGens i * cliffordGens i = (signatureVec p q i) • (1 : EndH H)
  clifford_anticomm : ∀ i j : Fin (p + q), i ≠ j →
    cliffordGens i * cliffordGens j + cliffordGens j * cliffordGens i = 0
  clifford_kreinAdj : ∀ i : Fin (p + q),
    ContinuousLinearMap.adjoint (cliffordGens i) = (signatureVec p q i) • cliffordGens i
  clifford_commutes_left : ∀ (i : Fin (p + q)) (a : A),
    cliffordGens i * base.π a = base.π a * cliffordGens i
  clifford_commutes_right : ∀ (i : Fin (p + q)) (b : B),
    cliffordGens i * base.ρ b = base.ρ b * cliffordGens i

namespace KasparovRealGradedCliffordCycle

/--
Induced real algebra homomorphism `Cl_{p,q} →ₐ[ℝ] EndH H` from a `KasparovRealGradedCliffordCycle`
(`S3-24`, Kasparov 1980; `R3.1`).
-/
def cliffordAlgHom
    {p q : ℕ} {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (C : KasparovRealGradedCliffordCycle p q A B H) : Clpq p q →ₐ[ℝ] EndH H :=
  CliffordAlgebra.lift (signatureQForm p q)
    ⟨{ toFun := fun v => ∑ i : Fin (p + q), v i • C.cliffordGens i
       map_add' := fun u v => by
         simp [add_smul, Finset.sum_add_distrib]
       map_smul' := fun r u => by
         simp [Finset.smul_sum, smul_smul] },
     fun v => by
       have hsum :
           (∑ i : Fin (p + q), v i • C.cliffordGens i) *
               (∑ j : Fin (p + q), v j • C.cliffordGens j) =
             (∑ i : Fin (p + q), (v i * v i) • (C.cliffordGens i * C.cliffordGens i)) +
               ∑ i : Fin (p + q), ∑ j ∈ Finset.univ.erase i,
                 (v i * v j) • (C.cliffordGens i * C.cliffordGens j) := by
         rw [Finset.sum_mul]
         simp_rw [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
         have hsplit : ∀ i : Fin (p + q),
             (∑ j : Fin (p + q), (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) =
               (v i * v i) • (C.cliffordGens i * C.cliffordGens i) +
                 ∑ j ∈ Finset.univ.erase i, (v i * v j) • (C.cliffordGens i * C.cliffordGens j) := by
           intro i
           exact (Finset.add_sum_erase Finset.univ
             (fun j => (v i * v j) • (C.cliffordGens i * C.cliffordGens j))
             (Finset.mem_univ i)).symm
         simp_rw [hsplit, Finset.sum_add_distrib]
       have hdiag :
           (∑ i : Fin (p + q), (v i * v i) • (C.cliffordGens i * C.cliffordGens i)) =
             algebraMap ℝ (EndH H) (signatureQForm p q v) := by
         simp_rw [C.clifford_sq, smul_smul, Algebra.algebraMap_eq_smul_one,
           signatureQForm, QuadraticMap.weightedSumSquares_apply, Finset.sum_smul]
         refine Finset.sum_congr rfl fun i _ => ?_
         congr 1
         ring
       have hoff :
           (∑ i : Fin (p + q), ∑ j ∈ Finset.univ.erase i,
             (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) = 0 := by
         have h2 :
             (2 : ℝ) • (∑ i : Fin (p + q), ∑ j ∈ Finset.univ.erase i,
               (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) = 0 := by
           have hswap :
               (∑ i : Fin (p + q), ∑ j ∈ Finset.univ.erase i,
                 (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) =
               ∑ j : Fin (p + q), ∑ i ∈ Finset.univ.erase j,
                 (v i * v j) • (C.cliffordGens i * C.cliffordGens j) := by
             have hfilter : ∀ i : Fin (p + q),
                 (∑ j ∈ Finset.univ.erase i,
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) =
                 ∑ j : Fin (p + q), if j = i then 0 else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j) := by
               intro i
               rw [← Finset.add_sum_erase Finset.univ
                 (fun j => if j = i then (0 : EndH H) else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j))
                 (Finset.mem_univ i)]
               simp only [↓reduceIte, zero_add]
               refine Finset.sum_congr rfl fun j hj => ?_
               simp [(Finset.mem_erase.mp hj).1]
             have hfilter2 : ∀ j : Fin (p + q),
                 (∑ i ∈ Finset.univ.erase j,
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) =
                 ∑ i : Fin (p + q), if i = j then 0 else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j) := by
               intro j
               rw [← Finset.add_sum_erase Finset.univ
                 (fun i => if i = j then (0 : EndH H) else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j))
                 (Finset.mem_univ j)]
               simp only [↓reduceIte, zero_add]
               refine Finset.sum_congr rfl fun i hi => ?_
               simp [(Finset.mem_erase.mp hi).1]
             calc
               (∑ i : Fin (p + q), ∑ j ∈ Finset.univ.erase i,
                 (v i * v j) • (C.cliffordGens i * C.cliffordGens j)) =
                 ∑ i : Fin (p + q), ∑ j : Fin (p + q), if j = i then (0 : EndH H) else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j) :=
                 Finset.sum_congr rfl fun i _ => hfilter i
               _ = ∑ j : Fin (p + q), ∑ i : Fin (p + q), if j = i then (0 : EndH H) else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j) := Finset.sum_comm
               _ = ∑ j : Fin (p + q), ∑ i : Fin (p + q), if i = j then (0 : EndH H) else
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j) :=
                 Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
                   by_cases hij : i = j
                   · subst hij; simp
                   · simp [hij, Ne.symm hij]
               _ = ∑ j : Fin (p + q), ∑ i ∈ Finset.univ.erase j,
                   (v i * v j) • (C.cliffordGens i * C.cliffordGens j) :=
                 Finset.sum_congr rfl fun j _ => (hfilter2 j).symm
           rw [two_smul]
           nth_rw 2 [hswap]
           rw [← Finset.sum_add_distrib]
           refine Finset.sum_eq_zero fun i _ => ?_
           rw [← Finset.sum_add_distrib]
           refine Finset.sum_eq_zero fun j hj => ?_
           have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
           have hanti := C.clifford_anticomm i j hne
           calc
             (v i * v j) • (C.cliffordGens i * C.cliffordGens j) +
                 (v j * v i) • (C.cliffordGens j * C.cliffordGens i) =
                 (v i * v j) • (C.cliffordGens i * C.cliffordGens j +
                   C.cliffordGens j * C.cliffordGens i) := by
               rw [mul_comm (v j) (v i), smul_add]
             _ = 0 := by rw [hanti, smul_zero]
         have hinv := congrArg (fun T : EndH H => ((2 : ℝ)⁻¹) • T) h2
         simpa [smul_smul] using hinv
       change (∑ i : Fin (p + q), v i • C.cliffordGens i) *
           (∑ j : Fin (p + q), v j • C.cliffordGens j) = _
       rw [hsum, hdiag, hoff, add_zero]⟩

/--
Every even product `e_i e_j` in a `KasparovRealGradedCliffordCycle` acts as an even operator
(`S3-24`, Kasparov 1980; `R3.1`).
-/
theorem even_acts_even
    {p q : ℕ} {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (C : KasparovRealGradedCliffordCycle p q A B H)
    (i j : Fin (p + q)) :
    KreinGradedModule.IsEven (H := H) (C.cliffordGens i * C.cliffordGens j) := by
  unfold KreinGradedModule.IsEven KreinGradedModule.gradeConj
  have h_inv : ∀ w : H,
      KreinGradedModule.gradeCLM (H := H) (KreinGradedModule.gradeCLM (H := H) w) = w :=
    KreinGradedModule.grade_invol
  have hi : (KreinGradedModule.gradeCLM (H := H)).comp
      ((C.cliffordGens i).comp (KreinGradedModule.gradeCLM (H := H))) = -C.cliffordGens i :=
    C.clifford_odd i
  have hj : (KreinGradedModule.gradeCLM (H := H)).comp
      ((C.cliffordGens j).comp (KreinGradedModule.gradeCLM (H := H))) = -C.cliffordGens j :=
    C.clifford_odd j
  apply ContinuousLinearMap.ext
  intro u
  have hju : KreinGradedModule.gradeCLM (H := H)
      (C.cliffordGens j (KreinGradedModule.gradeCLM (H := H) u)) = -(C.cliffordGens j u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH H => T u) hj
  have hiu : KreinGradedModule.gradeCLM (H := H)
      (C.cliffordGens i (KreinGradedModule.gradeCLM (H := H) (C.cliffordGens j u))) =
      -(C.cliffordGens i (C.cliffordGens j u)) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH H => T (C.cliffordGens j u)) hi
  calc
    ((KreinGradedModule.gradeCLM (H := H)).comp
        ((C.cliffordGens i * C.cliffordGens j).comp (KreinGradedModule.gradeCLM (H := H)))) u
        = KreinGradedModule.gradeCLM (H := H) (C.cliffordGens i
            (C.cliffordGens j (KreinGradedModule.gradeCLM (H := H) u))) := rfl
    _ = KreinGradedModule.gradeCLM (H := H) (C.cliffordGens i
          (KreinGradedModule.gradeCLM (H := H) (KreinGradedModule.gradeCLM (H := H)
            (C.cliffordGens j (KreinGradedModule.gradeCLM (H := H) u))))) := by
      rw [h_inv]
    _ = KreinGradedModule.gradeCLM (H := H) (C.cliffordGens i
          (KreinGradedModule.gradeCLM (H := H) (-(C.cliffordGens j u)))) := by
      rw [hju]
    _ = -(KreinGradedModule.gradeCLM (H := H) (C.cliffordGens i
          (KreinGradedModule.gradeCLM (H := H) (C.cliffordGens j u)))) := by
      simp only [map_neg]
    _ = (C.cliffordGens i * C.cliffordGens j) u := by
      rw [hiu, neg_neg]
      rfl

end KasparovRealGradedCliffordCycle

/--
Koszul `ℤ₂`-graded supercommutativity on the real split tower (`S3-24`, Kasparov 1980; `R3.1`,
`R3.3`): odd operators anticommute in the supercommutator (`[X, Y]_s = X Y + Y X`), while
odd-even pairs commute up to ordinary commutator.
-/
theorem clSplitTower_koszulTensor_supercommute
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    {X Y E : EndH H}
    (hX : KreinGradedModule.IsOdd (H := H) X)
    (hY : KreinGradedModule.IsOdd (H := H) Y)
    (hE : KreinGradedModule.IsEven (H := H) E) :
    KreinGradedModule.superComm (H := H) X Y = X * Y + Y * X ∧
      KreinGradedModule.superComm (H := H) X E = X * E - E * X := by
  refine ⟨?_, ?_⟩
  · rw [KreinGradedModule.superComm_odd_odd (H := H) hX hY]
    rfl
  · rw [KreinGradedModule.superComm_odd_even (H := H) hX hE]
    rfl

/--
Concrete `Cl_{1,1}` Kasparov graded Clifford cycle at stage `n` of the real split Krein tower
(`S3-24`, Kasparov 1980; `R3.1`, `R3.3`; T17 inhabitant). Uses `(cl11.eps, cl11.K)` as the
`(+1, -1)` odd Clifford generators on `StageKreinH n`.
-/
def stageKasparovCliffordCycle (n : ℕ) :
    KasparovRealGradedCliffordCycle 1 1 (EndH (StageVec n)) ℝ (StageKreinH n) where
  base := clSplitStageCycle n
  cliffordGens := fun i =>
    if i.1 = 0 then (clSplitStageCycle n).cl11.eps else (clSplitStageCycle n).cl11.K
  clifford_odd := fun i => by
    have heps : (clSplitStageCycle n).cl11.eps =
        SplitDoubledSpace.splitDoubledSpectralEpsilon (E := StageVec n) := rfl
    have hK : (clSplitStageCycle n).cl11.K =
        SplitDoubledSpace.splitDoubledComplexI (E := StageVec n) := by
      change (SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)).K = _
      exact SplitDoubledSpace.splitDoubledCl11Action_K
    have hgrade : KreinGradedModule.gradeCLM (H := StageKreinH n) =
        SplitDoubledSpace.splitDoubledModularJ (E := StageVec n) := rfl
    fin_cases i
    · dsimp [KreinGradedModule.IsOdd, KreinGradedModule.gradeConj]
      rw [heps, hgrade]
      apply ContinuousLinearMap.ext
      intro u
      apply SplitDoubledSpace.ext
      apply DoubledSpace.ext <;>
        simp [SplitDoubledSpace.splitDoubledModularJ, SplitDoubledSpace.splitDoubledSpectralEpsilon,
          SplitDoubledSpace.conjEnd_apply, modular_j_apply, spectral_epsilon_apply]
    · dsimp [KreinGradedModule.IsOdd, KreinGradedModule.gradeConj]
      rw [hK, hgrade]
      apply ContinuousLinearMap.ext
      intro u
      apply SplitDoubledSpace.ext
      apply DoubledSpace.ext <;>
        simp [SplitDoubledSpace.splitDoubledModularJ, SplitDoubledSpace.splitDoubledComplexI,
          SplitDoubledSpace.conjEnd_apply, modular_j_apply, complex_i_apply]
  clifford_sq := fun i => by
    fin_cases i
    · dsimp [signatureVec]
      rw [one_smul, ContinuousLinearMap.mul_def]
      exact (clSplitStageCycle n).cl11.eps_sq
    · dsimp [signatureVec]
      rw [neg_one_smul, ContinuousLinearMap.mul_def]
      exact (clSplitStageCycle n).cl11.K_sq
  clifford_anticomm := fun i j hij => by
    have heps : (clSplitStageCycle n).cl11.eps =
        SplitDoubledSpace.splitDoubledSpectralEpsilon (E := StageVec n) := rfl
    have hK : (clSplitStageCycle n).cl11.K =
        SplitDoubledSpace.splitDoubledComplexI (E := StageVec n) := by
      change (SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)).K = _
      exact SplitDoubledSpace.splitDoubledCl11Action_K
    fin_cases i <;> fin_cases j <;> simp_all
    · apply ContinuousLinearMap.ext
      intro u
      apply SplitDoubledSpace.ext
      apply DoubledSpace.ext <;>
        simp [SplitDoubledSpace.splitDoubledSpectralEpsilon,
          SplitDoubledSpace.splitDoubledComplexI, SplitDoubledSpace.conjEnd_apply,
          spectral_epsilon_apply, complex_i_apply]
    · apply ContinuousLinearMap.ext
      intro u
      apply SplitDoubledSpace.ext
      apply DoubledSpace.ext <;>
        simp [SplitDoubledSpace.splitDoubledSpectralEpsilon,
          SplitDoubledSpace.splitDoubledComplexI, SplitDoubledSpace.conjEnd_apply,
          spectral_epsilon_apply, complex_i_apply]
  clifford_kreinAdj := fun i => by
    have heps : (clSplitStageCycle n).cl11.eps =
        SplitDoubledSpace.splitDoubledSpectralEpsilon (E := StageVec n) := rfl
    have hK : (clSplitStageCycle n).cl11.K =
        SplitDoubledSpace.splitDoubledComplexI (E := StageVec n) := by
      change (SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)).K = _
      exact SplitDoubledSpace.splitDoubledCl11Action_K
    fin_cases i
    · dsimp [signatureVec]
      rw [one_smul, heps]
      symm
      refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
      simp [SplitDoubledSpace.inner_eq, SplitDoubledSpace.splitDoubledSpectralEpsilon,
        SplitDoubledSpace.conjEnd_apply, WithLp.prod_inner_apply, spectral_epsilon_apply]
    · dsimp [signatureVec]
      rw [neg_one_smul, hK]
      symm
      refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
      change ⟪(-(SplitDoubledSpace.splitDoubledComplexI (E := StageVec n))) u, v⟫_ℝ =
        ⟪u, SplitDoubledSpace.splitDoubledComplexI (E := StageVec n) v⟫_ℝ
      rw [neg_apply, inner_neg_left, SplitDoubledSpace.inner_eq,
        SplitDoubledSpace.inner_eq, SplitDoubledSpace.splitDoubledComplexI,
        SplitDoubledSpace.conjEnd_apply, SplitDoubledSpace.conjEnd_apply,
        WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      simp only [complex_i_apply, inner_neg_left, inner_neg_right]
      change -(-⟪WithLp.snd u.toDoubled, WithLp.fst v.toDoubled⟫_ℝ +
          ⟪WithLp.fst u.toDoubled, WithLp.snd v.toDoubled⟫_ℝ) =
        -⟪WithLp.fst u.toDoubled, WithLp.snd v.toDoubled⟫_ℝ +
          ⟪WithLp.snd u.toDoubled, WithLp.fst v.toDoubled⟫_ℝ
      ring
  clifford_commutes_left := fun i a => by
    have heps : (clSplitStageCycle n).cl11.eps =
        SplitDoubledSpace.splitDoubledSpectralEpsilon (E := StageVec n) := rfl
    have hK : (clSplitStageCycle n).cl11.K =
        SplitDoubledSpace.splitDoubledComplexI (E := StageVec n) := by
      change (SplitDoubledSpace.splitDoubledCl11Action (E := StageVec n)).K = _
      exact SplitDoubledSpace.splitDoubledCl11Action_K
    have hdiag : ∀ u : StageKreinH n, ((clSplitStageCycle n).π a u).toDoubled =
        to_doubled (a (WithLp.fst u.toDoubled)) (a (WithLp.snd u.toDoubled)) := fun _ => rfl
    fin_cases i
    · dsimp
      rw [heps]
      apply ContinuousLinearMap.ext
      intro u
      apply SplitDoubledSpace.ext
      apply DoubledSpace.ext <;>
        simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
          SplitDoubledSpace.splitDoubledSpectralEpsilon, SplitDoubledSpace.conjEnd_apply,
          hdiag, spectral_epsilon_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_neg]
    · dsimp
      rw [hK]
      apply ContinuousLinearMap.ext
      intro u
      apply SplitDoubledSpace.ext
      apply DoubledSpace.ext <;>
        simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
          SplitDoubledSpace.splitDoubledComplexI, SplitDoubledSpace.conjEnd_apply,
          hdiag, complex_i_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_neg]
  clifford_commutes_right := fun i b => by
    fin_cases i <;> simp [clSplitStageCycle, Algebra.algebraMap_eq_smul_one]

/--
Closed T16 non-commutativity witness for `EndH (StageKreinH 1)` (`S3-24`; `R3.1`).
-/
theorem endH_stageKrein1_noncomm :
    ∃ A B : EndH (StageKreinH 1), A * B ≠ B * A :=
  ⟨KreinSpace.jCLM (H := StageKreinH 1), KreinGradedModule.gradeCLM (H := StageKreinH 1),
    fun h => by
      let u0 : StageKreinH 1 := ⟨to_doubled (WithLp.toLp 2 (fun _ : Fin (2 ^ 1) => (1 : ℝ))) 0⟩
      have hval := congrArg (fun T : EndH (StageKreinH 1) =>
        (WithLp.snd (T u0).toDoubled) 0) h
      norm_num [u0, ContinuousLinearMap.mul_def,
        SplitDoubledSpace.jCLM_eq_splitDoubledSpectralEpsilon,
        SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
        SplitDoubledSpace.splitDoubledSpectralEpsilon,
        SplitDoubledSpace.splitDoubledModularJ, SplitDoubledSpace.conjEnd_apply,
        spectral_epsilon_apply, modular_j_apply] at hval⟩

/--
Equivariant analytical index invariance for a `KasparovRealGradedCliffordCycle` under
grading- and phase-intertwiners (`S3-24`, Kasparov 1980 / `RealSplitKreinEquivarianceBridge`;
`R3.3`).
-/
theorem kasparovCliffordCycle_equivariant_analyticalIndex
    {p q : ℕ} {A₁ A₂ B₁ B₂ H₁ H₂ : Type*}
    [NormedRing A₁] [NormedRing B₁] [NormedAlgebra ℝ A₁] [NormedAlgebra ℝ B₁]
    [NormedRing A₂] [NormedRing B₂] [NormedAlgebra ℝ A₂] [NormedAlgebra ℝ B₂]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [KreinSpace H₁] [KreinGradedModule H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (C₁ : KasparovRealGradedCliffordCycle p q A₁ B₁ H₁)
    (C₂ : KasparovRealGradedCliffordCycle p q A₂ B₂ H₂)
    (U : H₁ ≃ₗ[ℝ] H₂)
    (hF : ∀ v : H₁, C₂.base.F (U v) = U (C₁.base.F v))
    (hGrade : ∀ v : H₁,
      KreinGradedModule.gradeCLM (H := H₂) (U v) =
        U (KreinGradedModule.gradeCLM (H := H₁) v))
    (hSurf : C₁.base.ChiralFredholmSurface) :
    C₂.base.ChiralFredholmSurface ∧
      ∀ hSurf₂ : C₂.base.ChiralFredholmSurface,
        C₁.base.analyticalIndex hSurf = C₂.base.analyticalIndex hSurf₂ :=
  analyticalIndex_eq_of_intertwiner (X := C₁.base) (Y := C₂.base) U hF hGrade hSurf

end KasparovClifford

/-! ## Part 3 (`S3-25`..`S3-28`): KO-Signs, Fundamental Symmetries, & Pseudo-Riemannian Krein Triples -/

section PseudoRiemannianKrein

/--
Connes (1995) even-dimension KO sign triple `(ε, ε', ε'')` where `J^2 = ε`, `J D = ε' D J`, and
`J χ = ε'' χ J` (`S3-25`, Connes 1995, §2; `R3.1`).
-/
structure Connes1995EvenSigns where
  eps : ℝ
  epsPrime : ℝ
  epsDoublePrime : ℝ
  eps_sq : eps * eps = 1
  epsPrime_sq : epsPrime * epsPrime = 1
  epsDoublePrime_sq : epsDoublePrime * epsDoublePrime = 1

attribute [ext] Connes1995EvenSigns

/--
Connes (1995) sign table for even KO-dimensions `0, 2, 4, 6 mod 8` (`S3-25`, Connes 1995;
`R3.1`; T17 inhabitant).
-/
def connes1995SignTable : Fin 4 → Connes1995EvenSigns
  | ⟨0, _⟩ => ⟨1, 1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨1, _⟩ => ⟨-1, 1, -1, by norm_num, by norm_num, by norm_num⟩
  | ⟨2, _⟩ => ⟨-1, 1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨3, _⟩ => ⟨1, 1, -1, by norm_num, by norm_num, by norm_num⟩

/--
Constructive default inhabitant for `Connes1995EvenSigns` (`KO`-dimension `0`, `S3-25`; T17
inhabitant).
-/
instance instInhabitedConnes1995EvenSigns : Inhabited Connes1995EvenSigns :=
  ⟨connes1995SignTable 0⟩

/--
Paschke–Sitarz (2006) KO sign triple `(ε, ε', ε'')` using the swapped convention `J D = ε D J`
and `J^2 = ε'` (`S3-26`, Paschke–Sitarz 2006, Eq. (1)–(3); `R3.1`).
-/
structure PaschkeSitarzKOSigns where
  eps : ℝ
  epsPrime : ℝ
  epsDoublePrime : ℝ
  eps_sq : eps * eps = 1
  epsPrime_sq : epsPrime * epsPrime = 1
  epsDoublePrime_sq : epsDoublePrime * epsDoublePrime = 1

attribute [ext] PaschkeSitarzKOSigns

/--
Paschke–Sitarz (2006) 8-periodic KO-dimension sign table (`S3-26`, Paschke–Sitarz 2006; `R3.1`;
T17 inhabitant).
-/
def paschkeSitarzSignTable : Fin 8 → PaschkeSitarzKOSigns
  | ⟨0, _⟩ => ⟨1, 1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨1, _⟩ => ⟨-1, 1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨2, _⟩ => ⟨1, -1, -1, by norm_num, by norm_num, by norm_num⟩
  | ⟨3, _⟩ => ⟨1, -1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨4, _⟩ => ⟨1, -1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨5, _⟩ => ⟨-1, -1, 1, by norm_num, by norm_num, by norm_num⟩
  | ⟨6, _⟩ => ⟨1, 1, -1, by norm_num, by norm_num, by norm_num⟩
  | ⟨7, _⟩ => ⟨1, 1, 1, by norm_num, by norm_num, by norm_num⟩

/--
Explicit equivalence `PaschkeSitarzKOSigns ≃ SpectralTriple.KOSigns` swapping `eps ↔ epsPrime`
(`S3-25`, `S3-26`; `R3.1`, `R3.3`).
-/
def paschkeSitarz_equiv_connes1996 : PaschkeSitarzKOSigns ≃ KOSigns where
  toFun s :=
    { epsJ := s.epsPrime
      epsD := s.eps
      epsChi := s.epsDoublePrime
      epsJ_sq := s.epsPrime_sq
      epsD_sq := s.eps_sq
      epsChi_sq := s.epsDoublePrime_sq }
  invFun s :=
    { eps := s.epsD
      epsPrime := s.epsJ
      epsDoublePrime := s.epsChi
      eps_sq := s.epsD_sq
      epsPrime_sq := s.epsJ_sq
      epsDoublePrime_sq := s.epsChi_sq }
  left_inv := fun ⟨_, _, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _, _⟩ => rfl

/--
Embedding of Connes (1995) even signs into `SpectralTriple.KOSigns` (`S3-25`, Connes 1995/1996;
`R3.1`, `R3.3`).
-/
def connes1995_to_connes1996 (s : Connes1995EvenSigns) : KOSigns where
  epsJ := s.eps
  epsD := s.epsPrime
  epsChi := s.epsDoublePrime
  epsJ_sq := s.eps_sq
  epsD_sq := s.epsPrime_sq
  epsChi_sq := s.epsDoublePrime_sq

/--
Agreement of Paschke–Sitarz even-dimension KO signs with Connes (1995)/(1996) under `eps ↔ epsPrime`
(`S3-25`, `S3-26`; `R3.1`).
-/
theorem paschkeSitarzTable_even_matches_connes1995 (k : Fin 4) :
    paschkeSitarz_equiv_connes1996 (paschkeSitarzSignTable ⟨2 * k.1, by omega⟩) =
      connes1995_to_connes1996 (connes1995SignTable k) := by
  rcases k with ⟨k, hk⟩
  interval_cases k <;> simp [paschkeSitarz_equiv_connes1996, paschkeSitarzSignTable,
    connes1995_to_connes1996, connes1995SignTable]

/--
Strohmaier (2006) skew-adjoint fundamental symmetry `J_sym^2 = -1`, `J_sym* = -J_sym` commuting
with the phase axis `K` (`S3-27`, Strohmaier 2006; `R3.1`).
-/
@[ext]
structure SkewFundamentalSymmetry
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : PhaseAxis H) where
  J_sym : EndR H
  J_sym_sq : J_sym.comp J_sym = -(ContinuousLinearMap.id ℝ H)
  J_sym_skew : ContinuousLinearMap.adjoint J_sym = -J_sym
  J_sym_phase_linear : PhaseLinear K.K J_sym

/--
Van den Dungen–Paschke–Rennie (2013) self-adjoint fundamental symmetry `β^2 = 1`, `β* = β`
commuting with the phase axis `K` (`S3-28`, VPR 2013; `R3.1`).
-/
@[ext]
structure SelfAdjFundamentalSymmetry
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : PhaseAxis H) where
  beta : EndR H
  beta_sq : beta.comp beta = ContinuousLinearMap.id ℝ H
  beta_sa : ContinuousLinearMap.adjoint beta = beta
  beta_phase_linear : PhaseLinear K.K beta

/--
Explicit equivalence `SkewFundamentalSymmetry H K ≃ SelfAdjFundamentalSymmetry H K` via `β = K ∘ J_sym`
and inverse `J_sym = -(K ∘ β)` whenever `K* = -K` (`S3-27`, `S3-28`; `R3.1`).
-/
def skewToSelfAdjSymmetry_equiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : PhaseAxis H) (hK_skew : ContinuousLinearMap.adjoint K.K = -K.K) :
    SkewFundamentalSymmetry H K ≃ SelfAdjFundamentalSymmetry H K where
  toFun s :=
    { beta := K.K.comp s.J_sym
      beta_sq := by
        calc
          (K.K.comp s.J_sym).comp (K.K.comp s.J_sym) =
              K.K.comp ((s.J_sym.comp K.K).comp s.J_sym) := by
            simp only [ContinuousLinearMap.comp_assoc]
          _ = K.K.comp ((K.K.comp s.J_sym).comp s.J_sym) := by
            have hlin : s.J_sym.comp K.K = K.K.comp s.J_sym := s.J_sym_phase_linear
            rw [hlin]
          _ = (K.K.comp K.K).comp (s.J_sym.comp s.J_sym) := by
            simp only [ContinuousLinearMap.comp_assoc]
          _ = (-(ContinuousLinearMap.id ℝ H)).comp (-(ContinuousLinearMap.id ℝ H)) := by
            rw [K.K_square_neg, s.J_sym_sq]
          _ = ContinuousLinearMap.id ℝ H := by ext x; simp
      beta_sa := by
        rw [ContinuousLinearMap.adjoint_comp, s.J_sym_skew, hK_skew]
        ext x
        have hlin := congrArg (fun T : EndR H => T x) s.J_sym_phase_linear
        simpa [ContinuousLinearMap.comp_apply] using hlin
      beta_phase_linear := by
        change (K.K.comp s.J_sym).comp K.K = K.K.comp (K.K.comp s.J_sym)
        have hlin : s.J_sym.comp K.K = K.K.comp s.J_sym := s.J_sym_phase_linear
        rw [ContinuousLinearMap.comp_assoc, hlin] }
  invFun b :=
    { J_sym := -(K.K.comp b.beta)
      J_sym_sq := by
        calc
          (-(K.K.comp b.beta)).comp (-(K.K.comp b.beta)) =
              K.K.comp ((b.beta.comp K.K).comp b.beta) := by
            simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg,
              ContinuousLinearMap.comp_assoc]
          _ = (K.K.comp K.K).comp (b.beta.comp b.beta) := by
            have hlin : b.beta.comp K.K = K.K.comp b.beta := b.beta_phase_linear
            rw [hlin]
            simp only [ContinuousLinearMap.comp_assoc]
          _ = -(ContinuousLinearMap.id ℝ H) := by
            rw [K.K_square_neg, b.beta_sq]
            ext x
            simp
      J_sym_skew := by
        rw [map_neg, ContinuousLinearMap.adjoint_comp, b.beta_sa, hK_skew,
          ContinuousLinearMap.comp_neg]
        ext x
        have hlin := congrArg (fun T : EndR H => T x) b.beta_phase_linear
        simpa [ContinuousLinearMap.comp_apply] using congrArg Neg.neg hlin
      J_sym_phase_linear := by
        change (-(K.K.comp b.beta)).comp K.K = K.K.comp (-(K.K.comp b.beta))
        have hlin : b.beta.comp K.K = K.K.comp b.beta := b.beta_phase_linear
        rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
          ContinuousLinearMap.comp_assoc, hlin] }
  left_inv s := by
    ext x
    change (-((K.K.comp (K.K.comp s.J_sym)) x)) = s.J_sym x
    rw [← ContinuousLinearMap.comp_assoc, K.K_square_neg]
    simp
  right_inv b := by
    ext x
    change (K.K.comp (-(K.K.comp b.beta))) x = b.beta x
    rw [ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc, K.K_square_neg]
    simp

/--
Characterization of `KreinSpace.IsKreinSkewAdjoint D` as `(β ∘ D)* = -(β ∘ D)` when `jCLM = β`
(`S3-27`, `S3-28`; `R3.1`).
-/
theorem kreinSkewAdjoint_iff_betaSkewAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] (D : EndR H) :
    KreinSpace.IsKreinSkewAdjoint (H := H) D ↔
      ContinuousLinearMap.adjoint ((KreinSpace.jCLM (H := H)).comp D) =
        -((KreinSpace.jCLM (H := H)).comp D) := by
  rw [KreinSpace.isKreinSkewAdjoint_iff, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff (-((KreinSpace.jCLM (H := H)).comp D))
      ((KreinSpace.jCLM (H := H)).comp D)]
  constructor
  · intro h x y
    have hxy := h x y
    simp only [KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply] at hxy
    have hJ : ⟪KreinSpace.jCLM (H := H) x, D y⟫_ℝ = ⟪x, KreinSpace.jCLM (H := H) (D y)⟫_ℝ := by
      change ⟪KreinSpace.J x, D y⟫_ℝ = ⟪x, KreinSpace.J (D y)⟫_ℝ
      exact KreinSpace.J_selfAdj x (D y)
    rw [neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, inner_neg_left, ← hJ, neg_eq_iff_add_eq_zero]
    exact hxy
  · intro h x y
    have hxy := h x y
    simp only [KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply]
    have hJ : ⟪KreinSpace.jCLM (H := H) x, D y⟫_ℝ = ⟪x, KreinSpace.jCLM (H := H) (D y)⟫_ℝ := by
      change ⟪KreinSpace.J x, D y⟫_ℝ = ⟪x, KreinSpace.J (D y)⟫_ℝ
      exact KreinSpace.J_selfAdj x (D y)
    rw [neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, inner_neg_left, ← hJ, neg_eq_iff_add_eq_zero] at hxy
    exact hxy

/--
Characterization of `KreinSpace.IsKreinSelfAdjoint T` as `β$-self-adjointness `(β ∘ T)* = β ∘ T`
(`S3-27`, `S3-28`; `R3.1`).
-/
theorem kreinSelfAdjoint_iff_betaSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] (T : EndR H) :
    KreinSpace.IsKreinSelfAdjoint (H := H) T ↔
      ContinuousLinearMap.adjoint ((KreinSpace.jCLM (H := H)).comp T) =
        (KreinSpace.jCLM (H := H)).comp T := by
  rw [KreinSpace.isKreinSelfAdjoint_iff, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff ((KreinSpace.jCLM (H := H)).comp T)
      ((KreinSpace.jCLM (H := H)).comp T)]
  constructor
  · intro h x y
    have hxy := h x y
    simp only [KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply] at hxy
    have hJ : ⟪KreinSpace.jCLM (H := H) x, T y⟫_ℝ = ⟪x, KreinSpace.jCLM (H := H) (T y)⟫_ℝ := by
      change ⟪KreinSpace.J x, T y⟫_ℝ = ⟪x, KreinSpace.J (T y)⟫_ℝ
      exact KreinSpace.J_selfAdj x (T y)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hJ]
    exact hxy
  · intro h x y
    have hxy := h x y
    simp only [KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply]
    have hJ : ⟪KreinSpace.jCLM (H := H) x, T y⟫_ℝ = ⟪x, KreinSpace.jCLM (H := H) (T y)⟫_ℝ := by
      change ⟪KreinSpace.J x, T y⟫_ℝ = ⟪x, KreinSpace.J (T y)⟫_ℝ
      exact KreinSpace.J_selfAdj x (T y)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hJ] at hxy
    exact hxy

/--
Pseudo-Riemannian Krein spectral triple (`S3-27`, `S3-28`, Strohmaier 2006 / Van den
Dungen–Paschke–Rennie 2013; `R3.1`, `R3.3`). Keeps the phase axis `K`, skew fundamental
symmetry `J_sym` with `jCLM = K ∘ J_sym`, Connes real structure `J`, grading `χ`, and Krein
skew-adjoint Dirac operator `D`.
-/
structure PseudoRiemannianKreinTriple
    (A H : Type*) [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] where
  signs : KOSigns
  phaseAxis : PhaseAxis H
  K_skew : ContinuousLinearMap.adjoint phaseAxis.K = -phaseAxis.K
  skewSymmetry : SkewFundamentalSymmetry H phaseAxis
  jCLM_eq_K_comp_Jsym : KreinSpace.jCLM (H := H) = phaseAxis.K.comp skewSymmetry.J_sym
  realStructure : RealStructure H phaseAxis signs
  realStructureKreinCompatible : RealStructureKreinCompatible realStructure
  grading : ChiralGrading H phaseAxis signs
  J_chi_compatible : RealStructureChiralCompatible realStructure grading
  spectralGenerator : SpectralGenerator H
  D_kreinSkewAdjoint : KreinSpace.IsKreinSkewAdjoint (H := H) spectralGenerator.D
  D_compactResolvent : CompactResolventData spectralGenerator.D
  D_phase_linear : PhaseLinear phaseAxis.K spectralGenerator.D
  representedAlgebra : RepresentedAlgebra A H
  rep_phase_linear : ∀ a : A, PhaseLinear phaseAxis.K (representedAlgebra.rep a)
  orderZero : OrderZeroCondition representedAlgebra realStructure
  orderOne : OrderOneCondition representedAlgebra realStructure spectralGenerator
  D_odd : DiracOdd spectralGenerator grading
  J_D_compatible : RealStructureDiracCompatible realStructure spectralGenerator

namespace PseudoRiemannianKreinTriple

section Ops

variable {A H : Type*} [Ring A] [Star A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

/--
Associated VPR self-adjoint fundamental symmetry `β = K ∘ J_sym = jCLM` (`S3-28`; `R3.1`).
-/
def betaSymmetry (T : PseudoRiemannianKreinTriple A H) :
    SelfAdjFundamentalSymmetry H T.phaseAxis :=
  skewToSelfAdjSymmetry_equiv T.phaseAxis T.K_skew T.skewSymmetry

/--
`β` extracted from `T.betaSymmetry` equals `KreinSpace.jCLM` (`S3-28`; `R3.1`).
-/
theorem betaSymmetry_eq_jCLM (T : PseudoRiemannianKreinTriple A H) :
    T.betaSymmetry.beta = KreinSpace.jCLM (H := H) :=
  T.jCLM_eq_K_comp_Jsym.symm

/--
Wick-rotated Dirac operator `D_W = K ∘ D` (`S3-27`, `S3-28`; `R3.1`).
-/
def wickRotatedDirac (T : PseudoRiemannianKreinTriple A H) : EndR H :=
  T.phaseAxis.K.comp T.spectralGenerator.D

/--
Hilbert-symmetrized Dirac operator `β ∘ K ∘ D` (`S3-28`; `R3.1`).
-/
def hilbertSymmetrizedDirac (T : PseudoRiemannianKreinTriple A H) : EndR H :=
  T.betaSymmetry.beta.comp T.wickRotatedDirac

/--
Square `D^2` (`S3-28`; `R3.1`).
-/
def diracModulusSq (T : PseudoRiemannianKreinTriple A H) : EndR H :=
  T.spectralGenerator.D.comp T.spectralGenerator.D

/--
Curvature / fundamental-symmetry commutator defect `[β, D] = β D - D β` (`S3-28`, VPR 2013;
`R3.1`).
-/
def curvatureDefect (T : PseudoRiemannianKreinTriple A H) : EndR H :=
  commutator T.betaSymmetry.beta T.spectralGenerator.D

/--
The Wick-rotated Dirac operator `K ∘ D` is Krein self-adjoint (`(K ∘ D)♯ = K ∘ D`) (`S3-27`,
`S3-28`; `R3.1`).
-/
theorem wickRotatedDirac_isKreinSelfAdjoint (T : PseudoRiemannianKreinTriple A H) :
    KreinSpace.IsKreinSelfAdjoint (H := H) T.wickRotatedDirac := by
  rw [kreinSelfAdjoint_iff_betaSelfAdjoint, ← T.betaSymmetry_eq_jCLM]
  change ContinuousLinearMap.adjoint T.hilbertSymmetrizedDirac = T.hilbertSymmetrizedDirac
  have hD_skew := (kreinSkewAdjoint_iff_betaSkewAdjoint T.spectralGenerator.D).mp
    T.D_kreinSkewAdjoint
  rw [← T.betaSymmetry_eq_jCLM] at hD_skew
  have hK_comm : T.betaSymmetry.beta.comp T.phaseAxis.K = T.phaseAxis.K.comp T.betaSymmetry.beta :=
    T.betaSymmetry.beta_phase_linear
  have hKD : T.hilbertSymmetrizedDirac =
      T.phaseAxis.K.comp (T.betaSymmetry.beta.comp T.spectralGenerator.D) := by
    unfold hilbertSymmetrizedDirac wickRotatedDirac
    rw [← ContinuousLinearMap.comp_assoc, hK_comm, ContinuousLinearMap.comp_assoc]
  rw [hKD, ContinuousLinearMap.adjoint_comp, hD_skew, T.K_skew]
  ext x
  have hlin := congrArg (fun S : EndR H => S x) T.D_phase_linear
  have hKcomm_apply : T.betaSymmetry.beta (T.phaseAxis.K (T.spectralGenerator.D x)) =
      T.phaseAxis.K (T.betaSymmetry.beta (T.spectralGenerator.D x)) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun S : EndR H => S (T.spectralGenerator.D x)) hK_comm
  simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_apply] at hlin ⊢
  rw [hlin, hKcomm_apply]

/--
`wickRotatedDirac` satisfies `(K ∘ D)^2 = -(D^2)` (`S3-27`, `S3-28`; `R3.1`).
-/
theorem wickRotatedDirac_sq (T : PseudoRiemannianKreinTriple A H) :
    T.wickRotatedDirac.comp T.wickRotatedDirac = -T.diracModulusSq := by
  unfold wickRotatedDirac diracModulusSq
  calc
    (T.phaseAxis.K.comp T.spectralGenerator.D).comp (T.phaseAxis.K.comp T.spectralGenerator.D) =
        T.phaseAxis.K.comp ((T.spectralGenerator.D.comp T.phaseAxis.K).comp T.spectralGenerator.D) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = (T.phaseAxis.K.comp T.phaseAxis.K).comp
          (T.spectralGenerator.D.comp T.spectralGenerator.D) := by
      have hlin : T.spectralGenerator.D.comp T.phaseAxis.K =
          T.phaseAxis.K.comp T.spectralGenerator.D := T.D_phase_linear
      rw [hlin]
      simp only [ContinuousLinearMap.comp_assoc]
    _ = -(T.spectralGenerator.D.comp T.spectralGenerator.D) := by
      rw [T.phaseAxis.K_square_neg]
      ext x
      simp

/--
Hilbert-symmetrized Dirac operator `β ∘ K ∘ D` is Hilbert self-adjoint (`S3-28`, VPR 2013; `R3.1`).
-/
theorem hilbertSymmetrizedDirac_isSelfAdjoint (T : PseudoRiemannianKreinTriple A H) :
    ContinuousLinearMap.adjoint T.hilbertSymmetrizedDirac = T.hilbertSymmetrizedDirac := by
  have h := T.wickRotatedDirac_isKreinSelfAdjoint
  rw [kreinSelfAdjoint_iff_betaSelfAdjoint, ← T.betaSymmetry_eq_jCLM] at h
  exact h

/--
Project a `PseudoRiemannianKreinTriple` to `KreinPhaseRealSpectralTriple` (`S3-27`, `S3-28`;
`R3.3`).
-/
def toKreinPhaseRealSpectralTriple (T : PseudoRiemannianKreinTriple A H) :
    KreinPhaseRealSpectralTriple A H where
  signs := T.signs
  phaseAxis := T.phaseAxis
  realStructure := T.realStructure
  realStructureKreinCompatible := T.realStructureKreinCompatible
  grading := T.grading
  J_chi_compatible := T.J_chi_compatible
  spectralGenerator := T.spectralGenerator
  D_kreinSkewAdjoint := T.D_kreinSkewAdjoint
  D_compactResolvent := T.D_compactResolvent
  D_phase_linear := T.D_phase_linear
  representedAlgebra := T.representedAlgebra
  rep_phase_linear := T.rep_phase_linear
  orderZero := T.orderZero
  orderOne := T.orderOne
  D_odd := T.D_odd
  J_D_compatible := T.J_D_compatible
  traceBackend := none
  modularWeightBackend := none
  renormalizedBackend := none

end Ops

/--
Phase-preserving vs phase-reversing separation on a nontrivial Hilbert space (`S3-27`, `S3-28`;
`R3.1`): no operator `F` whose square is `±1` can simultaneously commute and anticommute with a
phase axis `K`.
-/
theorem phasePreserving_ne_phaseReversing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (K : PhaseAxis H) {F T : EndR H}
    (hF_sq : F.comp F = ContinuousLinearMap.id ℝ H ∨
      F.comp F = -(ContinuousLinearMap.id ℝ H))
    (hF_pres : PhaseLinear K.K F)
    (hT_rev : T.comp K.K = -(K.K.comp T)) :
    F ≠ T := by
  intro heq
  subst heq
  have hsum : F.comp K.K + F.comp K.K = 0 := by
    have h1 : F.comp K.K = K.K.comp F := hF_pres
    calc
      F.comp K.K + F.comp K.K = K.K.comp F + (-K.K.comp F) := by
        nth_rw 1 [h1]
        rw [hT_rev]
      _ = 0 := by ext x; simp
  have h2FK : (2 : ℝ) • (F.comp K.K) = 0 := by
    rw [two_smul]
    exact hsum
  have hFK0 : F.comp K.K = 0 := by
    have := congrArg (fun S : EndR H => ((2 : ℝ)⁻¹) • S) h2FK
    simpa [smul_smul] using this
  have hF0 : F = 0 := by
    have h1 : (F.comp K.K).comp K.K = 0 := by rw [hFK0, ContinuousLinearMap.zero_comp]
    rw [ContinuousLinearMap.comp_assoc, K.K_square_neg, ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.comp_id] at h1
    exact neg_eq_zero.mp h1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  rcases hF_sq with hpos | hneg
  · have := congrArg (fun S : EndR H => S x) hpos
    simp [hF0] at this
    exact hx this.symm
  · have := congrArg (fun S : EndR H => S x) hneg
    simp [hF0] at this
    exact hx this

/--
Strict separation of `K`, `J`, `β`, and `J_sym` inside a nontrivial `PseudoRiemannianKreinTriple`
(`S3-27`, `S3-28`; `R3.1`, `R3.3`).
-/
theorem operators_strictly_separated
    {A H : Type*} [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [Nontrivial H]
    (T : PseudoRiemannianKreinTriple A H) :
    T.phaseAxis.K ≠ (T.realStructure.J : EndR H) ∧
      T.phaseAxis.K ≠ T.betaSymmetry.beta ∧
      T.skewSymmetry.J_sym ≠ (T.realStructure.J : EndR H) := by
  have hKJ : T.phaseAxis.K ≠ (T.realStructure.J : EndR H) :=
    phasePreserving_ne_phaseReversing T.phaseAxis (Or.inr T.phaseAxis.K_square_neg)
      rfl T.realStructure.J_phase_reversing
  have hKβ : T.phaseAxis.K ≠ T.betaSymmetry.beta := by
    intro h
    have hsq := congrArg (fun S : EndR H => S.comp S) h
    rw [T.phaseAxis.K_square_neg, T.betaSymmetry.beta_sq] at hsq
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hx2 := congrArg (fun S : EndR H => S x) hsq
    simp only [neg_apply, ContinuousLinearMap.id_apply] at hx2
    have hx0 : x = 0 := by
      have hadd := add_eq_zero_iff_eq_neg.mpr hx2.symm
      rw [← two_smul ℝ x] at hadd
      exact (smul_eq_zero.mp hadd).resolve_left (by norm_num)
    exact hx hx0
  have hJsymJ : T.skewSymmetry.J_sym ≠ (T.realStructure.J : EndR H) :=
    phasePreserving_ne_phaseReversing T.phaseAxis (Or.inr T.skewSymmetry.J_sym_sq)
      T.skewSymmetry.J_sym_phase_linear T.realStructure.J_phase_reversing
  exact ⟨hKJ, hKβ, hJsymJ⟩

end PseudoRiemannianKreinTriple

/-! ### Concrete `KO = 0` Pseudo-Riemannian Krein Witness on `DoubledSpace (DoubledSpace ℝ)` -/

private abbrev D2H := DoubledSpace (DoubledSpace ℝ)

private lemma d2h_ext {u v : D2H}
    (h11 : WithLp.fst (WithLp.fst u) = WithLp.fst (WithLp.fst v))
    (h12 : WithLp.snd (WithLp.fst u) = WithLp.snd (WithLp.fst v))
    (h21 : WithLp.fst (WithLp.snd u) = WithLp.fst (WithLp.snd v))
    (h22 : WithLp.snd (WithLp.snd u) = WithLp.snd (WithLp.snd v)) : u = v :=
  DoubledSpace.ext (DoubledSpace.ext h11 h12) (DoubledSpace.ext h21 h22)

private def d2K : EndR D2H where
  toFun u := to_doubled (complex_i (WithLp.fst u)) (complex_i (WithLp.snd u))
  map_add' u v := by
    apply DoubledSpace.ext
    · simp [WithLp.add_fst, map_add]
    · simp [WithLp.add_snd, map_add]
  map_smul' r u := by
    apply DoubledSpace.ext
    · simp [WithLp.smul_fst, map_smul]
    · simp [WithLp.smul_snd, map_smul]
  cont := by
    refine (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
      (β := DoubledSpace ℝ)).comp ?_
    exact ((complex_i (E := ℝ)).continuous.comp
      (WithLp.continuous_fst (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
        (β := DoubledSpace ℝ))).prodMk
      ((complex_i (E := ℝ)).continuous.comp
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
          (β := DoubledSpace ℝ)))

private lemma d2h_inner (u v : D2H) :
    ⟪u, v⟫_ℝ =
      WithLp.fst (WithLp.fst u) * WithLp.fst (WithLp.fst v) +
        WithLp.snd (WithLp.fst u) * WithLp.snd (WithLp.fst v) +
        (WithLp.fst (WithLp.snd u) * WithLp.fst (WithLp.snd v) +
          WithLp.snd (WithLp.snd u) * WithLp.snd (WithLp.snd v)) := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change (WithLp.fst (WithLp.fst v) * WithLp.fst (WithLp.fst u) +
      WithLp.snd (WithLp.fst v) * WithLp.snd (WithLp.fst u)) +
    (WithLp.fst (WithLp.snd v) * WithLp.fst (WithLp.snd u) +
      WithLp.snd (WithLp.snd v) * WithLp.snd (WithLp.snd u)) = _
  ring

private def d2Jsym : EndR D2H where
  toFun u := to_doubled (-(complex_i (WithLp.fst u))) (complex_i (WithLp.snd u))
  map_add' u v := by
    apply DoubledSpace.ext
    · simp [WithLp.add_fst, map_add]
      rw [add_comm]
    · simp [WithLp.add_snd, map_add]
  map_smul' r u := by
    apply DoubledSpace.ext
    · simp [WithLp.smul_fst, map_smul, smul_neg]
    · simp [WithLp.smul_snd, map_smul]
  cont := by
    refine (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
      (β := DoubledSpace ℝ)).comp ?_
    exact (((complex_i (E := ℝ)).continuous.comp
      (WithLp.continuous_fst (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
        (β := DoubledSpace ℝ))).neg).prodMk
      ((complex_i (E := ℝ)).continuous.comp
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
          (β := DoubledSpace ℝ)))

private def d2Jreal : EndR D2H where
  toFun u := to_doubled (modular_j (WithLp.fst u)) (modular_j (WithLp.snd u))
  map_add' u v := by
    apply DoubledSpace.ext
    · simp [WithLp.add_fst, map_add]
    · simp [WithLp.add_snd, map_add]
  map_smul' r u := by
    apply DoubledSpace.ext
    · simp [WithLp.smul_fst, map_smul]
    · simp [WithLp.smul_snd, map_smul]
  cont := by
    refine (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
      (β := DoubledSpace ℝ)).comp ?_
    exact ((modular_j (E := ℝ)).continuous.comp
      (WithLp.continuous_fst (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
        (β := DoubledSpace ℝ))).prodMk
      ((modular_j (E := ℝ)).continuous.comp
        (WithLp.continuous_snd (p := (2 : ENNReal)) (α := DoubledSpace ℝ)
          (β := DoubledSpace ℝ)))

private def d2Dirac : EndR D2H := modular_j

@[simp] private lemma d2K_fst (u : D2H) : WithLp.fst (d2K u) = complex_i (WithLp.fst u) := rfl
@[simp] private lemma d2K_snd (u : D2H) : WithLp.snd (d2K u) = complex_i (WithLp.snd u) := rfl
@[simp] private lemma d2Jsym_fst (u : D2H) : WithLp.fst (d2Jsym u) = -(complex_i (WithLp.fst u)) := rfl
@[simp] private lemma d2Jsym_snd (u : D2H) : WithLp.snd (d2Jsym u) = complex_i (WithLp.snd u) := rfl
@[simp] private lemma d2Jreal_fst (u : D2H) : WithLp.fst (d2Jreal u) = modular_j (WithLp.fst u) := rfl
@[simp] private lemma d2Jreal_snd (u : D2H) : WithLp.snd (d2Jreal u) = modular_j (WithLp.snd u) := rfl

private lemma d2K_sq : d2K.comp d2K = -(ContinuousLinearMap.id ℝ D2H) := by
  apply ContinuousLinearMap.ext
  intro u
  apply d2h_ext <;> simp [complex_i_apply]

private lemma d2K_skew : ContinuousLinearMap.adjoint d2K = -d2K := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff (-d2K) d2K).2 fun u v => ?_
  simp only [neg_apply, d2h_inner, WithLp.neg_fst, WithLp.neg_snd, d2K_fst, d2K_snd,
    complex_i_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

private lemma d2Jsym_sq : d2Jsym.comp d2Jsym = -(ContinuousLinearMap.id ℝ D2H) := by
  apply ContinuousLinearMap.ext
  intro u
  apply d2h_ext <;> simp [complex_i_apply]

private lemma d2Jsym_skew : ContinuousLinearMap.adjoint d2Jsym = -d2Jsym := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff (-d2Jsym) d2Jsym).2 fun u v => ?_
  simp only [neg_apply, d2h_inner, WithLp.neg_fst, WithLp.neg_snd, d2Jsym_fst, d2Jsym_snd,
    complex_i_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

private lemma d2Jsym_phase_linear : PhaseLinear d2K d2Jsym := by
  apply ContinuousLinearMap.ext
  intro u
  apply d2h_ext <;> simp [complex_i_apply]

private lemma d2jCLM_eq : KreinSpace.jCLM (H := D2H) = d2K.comp d2Jsym := by
  apply ContinuousLinearMap.ext
  intro u
  apply d2h_ext <;>
    simp [jCLM_eq_spectral_epsilon, spectral_epsilon_apply, complex_i_apply]

private lemma d2Jreal_sq : d2Jreal.comp d2Jreal = ContinuousLinearMap.id ℝ D2H := by
  apply ContinuousLinearMap.ext
  intro u
  apply d2h_ext <;> simp [modular_j_apply]

private lemma d2Jreal_phase_reversing : d2Jreal.comp d2K = -(d2K.comp d2Jreal) := by
  apply ContinuousLinearMap.ext
  intro u
  apply d2h_ext <;> simp [complex_i_apply, modular_j_apply]

private lemma d2Jreal_kreinIsometry : KreinSpace.IsKreinIsometry (H := D2H) d2Jreal := by
  intro u v
  simp only [KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply, jCLM_eq_spectral_epsilon,
    spectral_epsilon_apply, d2h_inner, d2Jreal_fst, d2Jreal_snd, WithLp.toLp_fst, WithLp.toLp_snd,
    WithLp.neg_fst, WithLp.neg_snd, modular_j_apply]
  ring

private lemma d2Dirac_kreinSkew : KreinSpace.IsKreinSkewAdjoint (H := D2H) d2Dirac := by
  rw [KreinSpace.isKreinSkewAdjoint_iff]
  intro u v
  simp only [d2Dirac, KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply,
    jCLM_eq_spectral_epsilon, spectral_epsilon_apply, modular_j_apply, d2h_inner,
    WithLp.toLp_fst, WithLp.toLp_snd, WithLp.neg_fst, WithLp.neg_snd]
  ring

/--
Closed T16 non-commutativity witness for `EndR D2H` (`S3-28`; `R3.1`).
-/
theorem endR_d2H_noncomm : ∃ A B : EndR D2H, A.comp B ≠ B.comp A := by
  refine ⟨d2K, d2Jreal, fun h => ?_⟩
  let u0 : D2H := to_doubled (to_doubled (1 : ℝ) (0 : ℝ)) (to_doubled (0 : ℝ) (0 : ℝ))
  have hv := congrArg (fun T : EndR D2H => WithLp.fst (WithLp.fst (T u0))) h
  norm_num [d2K_fst, d2Jreal_fst, complex_i_apply, modular_j_apply, u0] at hv

/--
Concrete `KO = 0` `PseudoRiemannianKreinTriple` witness on `D2H = DoubledSpace (DoubledSpace ℝ)`
(`S3-27`, `S3-28`; `R3.1`, `R3.3`; T17 inhabitant).
-/
def splitDoubledPseudoRiemannianWitness : PseudoRiemannianKreinTriple ℝ D2H where
  signs :=
    { epsJ := 1
      epsD := 1
      epsChi := 1
      epsJ_sq := by norm_num
      epsD_sq := by norm_num
      epsChi_sq := by norm_num }
  phaseAxis :=
    { K := d2K
      K_square_neg := d2K_sq }
  K_skew := d2K_skew
  skewSymmetry :=
    { J_sym := d2Jsym
      J_sym_sq := d2Jsym_sq
      J_sym_skew := d2Jsym_skew
      J_sym_phase_linear := d2Jsym_phase_linear }
  jCLM_eq_K_comp_Jsym := d2jCLM_eq
  realStructure :=
    { J := ⟨d2Jreal, d2Jreal, d2Jreal_sq, d2Jreal_sq⟩
      J_square := by simpa using d2Jreal_sq
      J_phase_reversing := d2Jreal_phase_reversing }
  realStructureKreinCompatible := d2Jreal_kreinIsometry
  grading :=
    { chi := KreinSpace.jCLM (H := D2H)
      chi_phase_linear := by
        apply ContinuousLinearMap.ext
        intro u
        apply d2h_ext <;> simp [jCLM_eq_spectral_epsilon]
      chi_square_one := by
        rw [jCLM_eq_spectral_epsilon]
        apply ContinuousLinearMap.ext
        intro u
        apply d2h_ext <;> simp }
  J_chi_compatible := by
    change d2Jreal.comp (KreinSpace.jCLM (H := D2H)) =
      ((1 : ℝ) • (KreinSpace.jCLM (H := D2H))).comp d2Jreal
    apply ContinuousLinearMap.ext
    intro u
    apply d2h_ext <;> simp [jCLM_eq_spectral_epsilon, modular_j_apply]
  spectralGenerator := { D := d2Dirac }
  D_kreinSkewAdjoint := d2Dirac_kreinSkew
  D_compactResolvent :=
    { spectralParameter := 0
      resolvent := d2Dirac
      resolvent_comp_shift := by
        apply ContinuousLinearMap.ext
        intro u
        apply d2h_ext <;> simp [d2Dirac, modular_j_apply]
      shift_comp_resolvent := by
        apply ContinuousLinearMap.ext
        intro u
        apply d2h_ext <;> simp [d2Dirac, modular_j_apply]
      resolvent_compact := InfoGeometry.KK.isCompactEnd_of_finiteDimensional (H := D2H) d2Dirac }
  D_phase_linear := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [d2Dirac]
  representedAlgebra := { rep := Algebra.ofId ℝ (EndR D2H) }
  rep_phase_linear := fun a => by
    apply ContinuousLinearMap.ext
    intro u
    apply d2h_ext <;> simp [Algebra.algebraMap_eq_smul_one]
  orderZero := fun a b => by
    have hrep : ∀ c : ℝ, ((Algebra.ofId ℝ (EndR D2H) : ℝ →+* EndR D2H) c) =
        c • ContinuousLinearMap.id ℝ D2H := fun _ => rfl
    apply ContinuousLinearMap.ext
    intro u
    dsimp only [oppositeRep]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hrep, hrep]
    simp [smul_smul, mul_comm]
  orderOne := fun a b => by
    have hrep : ∀ c : ℝ, ((Algebra.ofId ℝ (EndR D2H) : ℝ →+* EndR D2H) c) =
        c • ContinuousLinearMap.id ℝ D2H := fun _ => rfl
    dsimp only [OperatorAlgebra.SpectralTriple.OrderOneCondition,
      OperatorAlgebra.SpectralTriple.commutator]
    rw [hrep]
    have hcomm : d2Dirac.comp (a • ContinuousLinearMap.id ℝ D2H) -
        (a • ContinuousLinearMap.id ℝ D2H).comp d2Dirac = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      simp
    rw [hcomm, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  D_odd := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [d2Dirac, jCLM_eq_spectral_epsilon]
  J_D_compatible := by
    change d2Jreal.comp d2Dirac = ((1 : ℝ) • d2Dirac).comp d2Jreal
    apply ContinuousLinearMap.ext
    intro u
    apply d2h_ext <;> simp [d2Dirac, modular_j_apply]

/--
Strict operator separation `(K ≠ J, K ≠ β, J_sym ≠ J)` for
`splitDoubledPseudoRiemannianWitness` (`S3-27`, `S3-28`; `R3.1`, `R3.3`).
-/
theorem splitDoubledPseudoRiemannianWitness_separation :
    splitDoubledPseudoRiemannianWitness.phaseAxis.K ≠
        (splitDoubledPseudoRiemannianWitness.realStructure.J : EndR D2H) ∧
      splitDoubledPseudoRiemannianWitness.phaseAxis.K ≠
        splitDoubledPseudoRiemannianWitness.betaSymmetry.beta ∧
      splitDoubledPseudoRiemannianWitness.skewSymmetry.J_sym ≠
        (splitDoubledPseudoRiemannianWitness.realStructure.J : EndR D2H) :=
  PseudoRiemannianKreinTriple.operators_strictly_separated splitDoubledPseudoRiemannianWitness

/--
Non-triviality of the Wick-rotated Dirac operator on `splitDoubledPseudoRiemannianWitness`
(`S3-28`; `R3.1`).
-/
theorem splitDoubledPseudoRiemannianWitness_wick_ne_zero :
    splitDoubledPseudoRiemannianWitness.wickRotatedDirac ≠ 0 := by
  intro h
  let u0 : D2H := to_doubled (to_doubled (1 : ℝ) (0 : ℝ)) (to_doubled (0 : ℝ) (0 : ℝ))
  have hv := congrArg (fun T : EndR D2H => WithLp.snd (WithLp.snd (T u0))) h
  norm_num [PseudoRiemannianKreinTriple.wickRotatedDirac, splitDoubledPseudoRiemannianWitness,
    d2K, d2Dirac, complex_i_apply, modular_j_apply, u0] at hv

/--
Constructive `SelfAdjFundamentalSymmetry` inhabitant on `D2H` (`S3-28`; `R3.1`; T17 inhabitant).
-/
def splitDoubledSelfAdjSymmetry :
    SelfAdjFundamentalSymmetry D2H splitDoubledPseudoRiemannianWitness.phaseAxis :=
  splitDoubledPseudoRiemannianWitness.betaSymmetry

/--
Constructive `SkewFundamentalSymmetry` inhabitant on `D2H` (`S3-27`; `R3.1`; T17 inhabitant).
-/
def splitDoubledSkewSymmetry :
    SkewFundamentalSymmetry D2H splitDoubledPseudoRiemannianWitness.phaseAxis :=
  splitDoubledPseudoRiemannianWitness.skewSymmetry

end PseudoRiemannianKrein

end InfoGeometry.KK.KreinSpectralTriplePrimary
