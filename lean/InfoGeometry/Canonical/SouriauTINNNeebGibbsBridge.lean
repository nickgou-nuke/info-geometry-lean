/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BarbarescoTINNDiscreteGENERICFoliation
import InfoGeometry.Canonical.NeebCoadjointOrbitGibbsClassification
import InfoGeometry.Canonical.SouriauCoadjointOrbitBridge
import InfoGeometry.Canonical.SU11MetriplecticCoadjointOrbit

/-!
# Canonical Bridge Unifying Barbaresco TINN GENERIC, Neeb Coadjoint Gibbs Orbits, and Souriau QGT

Constructs explicit bridges across four Lie-thermodynamic owners on `main`:
1. Identifies `BarbarescoTINN.affineLiePoissonBracket` with `SouriauKKS.affineKksForm` and
   `SouriauCoadjointOrbitBridge.coadjointAction`,
2. Instantiates `SouriauCoadjointOrbitBridge.souriauOnsagerSystem` and `souriauQGT` with the exact
   Fisher–Souriau calorific stiffness `1 / t²` derived from `Neeb.sl2_elliptic_heat_and_fisher_capacity`,
3. Discharges the abstract discrete-gradient hypothesis in `BarbarescoTINNDiscreteGENERICFoliation`
   constructively via the exact midpoint gradient `quadMidpointGrad` for symmetric quadratic energy
   and entropy functionals,
4. Connects the `SU(1,1)` Poincaré disk moment map `J1` from `SU11MetriplecticCoadjointOrbit`
   to the elliptic `sl₂(ℝ)` coadjoint Laplace integral domain `[ρ, ∞)` in `Neeb`.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Filter Set Matrix
open scoped Topology
open InfoGeometry.Canonical.BarbarescoTINNDiscreteGENERICFoliation
open InfoGeometry.Canonical.NeebCoadjointOrbitGibbsClassification
open InfoGeometry.Canonical.SouriauCoadjointOrbitBridge
open InfoGeometry.Canonical.SU11MetriplecticCoadjointOrbit

namespace InfoGeometry.Canonical.SouriauTINNNeebGibbsBridge

/-! ### Part 1: Affine Lie–Poisson Bracket ↔ Souriau KKS & Coadjoint Action -/

/-- Barbaresco's affine Lie–Poisson bracket is definitionally `SouriauKKS.affineKksForm`. -/
theorem affineLiePoissonBracket_eq_affineKksForm {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (μ : Module.Dual ℝ L) (θ : L →ₗ[ℝ] L →ₗ[ℝ] ℝ) (X Y : L) :
    affineLiePoissonBracket μ (fun A B => θ A B) X Y = SouriauKKS.affineKksForm μ θ X Y :=
  rfl

/-- At vanishing cocycle `θ = 0`, the affine Lie–Poisson bracket equals `-⟨ad*_X μ, Y⟩`. -/
theorem affineLiePoissonBracket_zero_eq_neg_coadjointAction {L : Type*} [LieRing L]
    [LieAlgebra ℝ L] (μ : Module.Dual ℝ L) (X Y : L) :
    affineLiePoissonBracket μ (fun _ _ => 0) X Y = -coadjointAction X μ Y := by
  change SouriauKKS.kksForm μ X Y + 0 = _
  rw [add_zero, kksForm_eq_neg_coadjointAction]

/-! ### Part 2: Souriau Onsager–Casimir System & QGT Powered by `sl₂(ℝ)` Massieu Capacity -/

/-- Rank-one Souriau–Fisher bilinear metric on a Lie algebra induced by the `sl₂(ℝ)` elliptic
calorific stiffness `1 / t²` along a character `α : Module.Dual ℝ L`. -/
def sl2FisherBilin {L : Type*} [AddCommGroup L] [Module ℝ L] (t : ℝ)
    (α : Module.Dual ℝ L) : L →ₗ[ℝ] L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => (1 / t ^ 2) * (α X * α Y))
    (fun X₁ X₂ Y => by simp only [map_add]; ring)
    (fun r X Y => by simp only [map_smul, smul_eq_mul]; ring)
    (fun X Y₁ Y₂ => by simp only [map_add]; ring)
    (fun r X Y => by simp only [map_smul, smul_eq_mul]; ring)

theorem sl2FisherBilin_symm {L : Type*} [AddCommGroup L] [Module ℝ L] (t : ℝ)
    (α : Module.Dual ℝ L) (X Y : L) :
    sl2FisherBilin t α X Y = sl2FisherBilin t α Y X := by
  simp only [sl2FisherBilin, LinearMap.mk₂_apply]
  ring

theorem sl2FisherBilin_nonneg {L : Type*} [AddCommGroup L] [Module ℝ L] (t : ℝ)
    (α : Module.Dual ℝ L) (X : L) :
    0 ≤ sl2FisherBilin t α X X := by
  simp only [sl2FisherBilin, LinearMap.mk₂_apply]
  exact mul_nonneg (one_div_nonneg.mpr (sq_nonneg t)) (mul_self_nonneg (α X))

/-- The scalar stiffness `1 / t²` in `sl2FisherBilin` is the exact derivative of the geometric heat
map `-ψ'(t) = λ₀ + 1 / t` on the elliptic `sl₂(ℝ)` coadjoint orbit for `t > 0`. -/
theorem sl2FisherBilin_eq_heat_capacity_mul {L : Type*} [AddCommGroup L] [Module ℝ L]
    (lam0 : ℝ) {t : ℝ} (ht : 0 < t) (α : Module.Dual ℝ L) (X Y : L) :
    HasDerivAt (fun u => -(lam0 + 1 / u)) (1 / t ^ 2) t ∧
      sl2FisherBilin t α X Y = (1 / t ^ 2) * (α X * α Y) :=
  ⟨(sl2_elliptic_heat_and_fisher_capacity lam0 ht).2.1, rfl⟩

/-- Instantiating `souriauOnsagerSystem` with `sl2FisherBilin t α` yields nonnegative quadratic
entropy production equal to `(1 / t²) * (α X)²`. -/
theorem sl2_souriau_onsager_entropy_production {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (t : ℝ) (α μ : Module.Dual ℝ L) (X : L) :
    (souriauOnsagerSystem (sl2FisherBilin t α) μ
        (sl2FisherBilin_symm t α) (sl2FisherBilin_nonneg t α)).totalGenerator X X =
      (1 / t ^ 2) * (α X * α X) ∧
    0 ≤ (souriauOnsagerSystem (sl2FisherBilin t α) μ
        (sl2FisherBilin_symm t α) (sl2FisherBilin_nonneg t α)).totalGenerator X X := by
  have h := souriauOnsagerSystem_entropy_production (sl2FisherBilin t α) μ
    (sl2FisherBilin_symm t α) (sl2FisherBilin_nonneg t α) X
  simpa [sl2FisherBilin] using h

/-- Explicit norm-squared formula for the Souriau Quantum Geometric Tensor driven by the `sl₂(ℝ)`
elliptic calorific Fisher metric. -/
theorem sl2_souriau_qgt_normSq {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (t : ℝ) (α μ : Module.Dual ℝ L) (X Y : L) :
    Complex.normSq (souriauQGT (sl2FisherBilin t α) μ X Y) =
      ((1 / t ^ 2) * (α X * α Y)) ^ 2 +
        (1 / 4 : ℝ) * (SouriauKKS.kksForm μ X Y) ^ 2 := by
  rw [souriauQGT_normSq]
  rfl

/-! ### Part 3: Constructive Quadratic Midpoint Gradient for Barbaresco TINN Integrators -/

/-- Homogeneous symmetric quadratic functional `Φ_A(z) = (1 / 2) ⟨z, A z⟩` on `ℝ^n`. -/
def quadFunctional {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct z (A.mulVec z)

/-- Constructive González / midpoint discrete gradient `(1 / 2) A (z + z')`. -/
def quadMidpointGrad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z z' : Fin n → ℝ) : Fin n → ℝ :=
  A.mulVec ((1 / 2 : ℝ) • (z + z'))

/-- Exact discrete-gradient secant identity for every symmetric matrix `Aᵀ = A`. -/
theorem quadMidpointGrad_exact {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hSym : Aᵀ = A)
    (z z' : Fin n → ℝ) :
    quadFunctional A z' - quadFunctional A z = dotProduct (quadMidpointGrad A z z') (z' - z) := by
  have hcross : dotProduct z' (A.mulVec z) = dotProduct z (A.mulVec z') := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSym]
  unfold quadFunctional quadMidpointGrad
  rw [Matrix.mulVec_smul, smul_dotProduct, Matrix.mulVec_add, add_dotProduct,
    dotProduct_sub, dotProduct_sub, dotProduct_comm (A.mulVec z) z', dotProduct_comm (A.mulVec z) z,
    dotProduct_comm (A.mulVec z') z', dotProduct_comm (A.mulVec z') z, hcross]
  simp only [smul_eq_mul]
  ring

/-- **Constructive Midpoint TINN First Law**:
any GENERIC step `z' - z = Δt (L dE + M dS)` driven by `dE = quadMidpointGrad A_E z z'` (`A_Eᵀ = A_E`)
strictly conserves `quadFunctional A_E z' = quadFunctional A_E z` for every step size `Δt`. -/
theorem tinn_quad_midpoint_first_law {n : ℕ}
    (A_E L M : Matrix (Fin n) (Fin n) ℝ) (z z' dS : Fin n → ℝ) (dt : ℝ)
    (hAE : A_Eᵀ = A_E)
    (hStep : z' - z = dt • genericVelocity L M (quadMidpointGrad A_E z z') dS)
    (hSkew : Lᵀ = -L) (hSymM : Mᵀ = M)
    (hDegenE : M.mulVec (quadMidpointGrad A_E z z') = 0) :
    quadFunctional A_E z' = quadFunctional A_E z :=
  tinn_discrete_first_law (quadFunctional A_E) L M z z' (quadMidpointGrad A_E z z') dS dt
    hStep (quadMidpointGrad_exact A_E hAE z z') hSkew hSymM hDegenE

/-- **Constructive Midpoint TINN Second Law**:
any GENERIC step `z' - z = Δt (L dE + M dS)` with `dt ≥ 0`, PSD `M`, and `dS = quadMidpointGrad A_S z z'`
(`A_Sᵀ = A_S`) monotonically preserves `quadFunctional A_S z ≤ quadFunctional A_S z'`. -/
theorem tinn_quad_midpoint_second_law {n : ℕ}
    (A_S L M : Matrix (Fin n) (Fin n) ℝ) (z z' dE : Fin n → ℝ) (dt : ℝ)
    (hAS : A_Sᵀ = A_S) (hdt : 0 ≤ dt)
    (hStep : z' - z = dt • genericVelocity L M dE (quadMidpointGrad A_S z z'))
    (hSkew : Lᵀ = -L) (hDegenS : L.mulVec (quadMidpointGrad A_S z z') = 0)
    (hPSD : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (M.mulVec v)) :
    quadFunctional A_S z ≤ quadFunctional A_S z' :=
  tinn_discrete_second_law_nonneg (quadFunctional A_S) L M z z' dE (quadMidpointGrad A_S z z') dt
    hdt hStep (quadMidpointGrad_exact A_S hAS z z') hSkew hDegenS hPSD

/-! ### Part 4: `SU(1,1)` Poincaré Disk Moment Range ↔ Elliptic `sl₂(ℝ)` Laplace Domain -/

/-- Every point `z` in the open Poincaré unit disk (`‖z‖² < 1`) maps under the `SU(1,1)` moment
component `J1 rho z` to a real value `≥ rho`, landing in the exact upper ray `[rho, ∞)` of
`Neeb.neeb_ex614_sl2_elliptic_laplace`. -/
theorem su11_J1_re_ge_rho {rho : ℝ} (hrho : 0 < rho) {z : ℂ} (hz : Complex.normSq z < 1) :
    rho ≤ (SU11MetriplecticCoadjointOrbit.J1 rho z).re := by
  have hJ1 : SU11MetriplecticCoadjointOrbit.J1 rho z =
      ((rho * (1 + Complex.normSq z) / (1 - Complex.normSq z) : ℝ) : ℂ) := by
    unfold SU11MetriplecticCoadjointOrbit.J1
    push_cast
    rfl
  rw [hJ1, Complex.ofReal_re]
  have hden : 0 < 1 - Complex.normSq z := sub_pos.mpr hz
  have hns : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hdiff :
      rho * (1 + Complex.normSq z) / (1 - Complex.normSq z) - rho =
        (2 * rho * Complex.normSq z) / (1 - Complex.normSq z) := by
    field_simp [hden.ne']
    ring
  have hnonneg : 0 ≤ (2 * rho * Complex.normSq z) / (1 - Complex.normSq z) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho.le) hns) hden.le
  linarith

/-- Shifted-ray Laplace integral on `Ioi rho` matching both the shifted `SU(1,1)` moment lower
bound `rho` and `Neeb.neeb_ex614_sl2_elliptic_laplace`. -/
theorem su11_disk_laplace_partition (rho : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi rho, Real.exp (-t * x)) = ∫ r in Ioi (0 : ℝ), Real.exp (-t * (rho + r)) ∧
      (∫ x in Ioi rho, Real.exp (-t * x)) = Real.exp (-t * rho) / t := by
  let F : ℝ → ℝ := fun x => -Real.exp (-t * x) / t
  have hderiv : ∀ x ∈ Ici rho, HasDerivAt F (Real.exp (-t * x)) x := by
    intro x _hx
    have harg : HasDerivAt (fun u : ℝ => -t * u) (-t * 1) x := (hasDerivAt_id x).const_mul (-t)
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-t * u)) (Real.exp (-t * x) * (-t * 1)) x :=
      harg.exp
    exact ((hexp.neg).div_const t).congr_deriv (by field_simp [ht.ne'])
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hlin : Tendsto (fun x : ℝ => t * x) atTop atTop :=
      Filter.tendsto_atTop.mpr fun B =>
        Filter.eventually_atTop.mpr ⟨B / t, fun x hx => by
          have hmul : t * (B / t) ≤ t * x := mul_le_mul_of_nonneg_left hx ht.le
          simpa [mul_div_cancel₀ B ht.ne'] using hmul⟩
    have hexp : Tendsto (fun x : ℝ => Real.exp (-t * x)) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    simpa [F] using (hexp.neg).div_const t
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-t * x)) (Ioi rho) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x _ => (Real.exp_pos _).le) hlim
  have hIoi : (∫ x in Ioi rho, Real.exp (-t * x)) = Real.exp (-t * rho) / t := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
    simp [F, neg_div]
  refine ⟨?_, hIoi⟩
  rw [hIoi, neeb_ex614_sl2_elliptic_laplace (lam0 := rho) ht]

end InfoGeometry.Canonical.SouriauTINNNeebGibbsBridge
