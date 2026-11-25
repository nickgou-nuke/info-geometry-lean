/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# Barbaresco Thermodynamics-Informed Neural Networks (TINN), Discrete GENERIC, & Souriau Foliation

Formalizes the core geometric and thermodynamic theorems of Frédéric Barbaresco's
*Thermodynamics-Informed Neural Networks: Transverse Symplectic Foliation Structure of
Souriau's Lie Groups Thermodynamics* (Source 4, Slides 20, 50–52, 130–138, 165–166, 170, 185–193):

1. **Continuous GENERIC / Metriplectic Structure**: skew Poisson matrix `Lᵀ = -L`, PSD dissipative
   matrix `M ≥ 0`, and degeneracy `L ∇S = 0`, `M ∇E = 0` imply exact energy conservation
   (`dE/dt = 0`) and nonnegative entropy production (`dS/dt ≥ 0`).
2. **Fluctuation-Dissipation Matrix Factorization (Slide 188)**: `M = (1 / (2 k_B)) B Bᵀ`
   automatically guarantees symmetry and positive semidefiniteness for any neural weight matrix `B`
   and `k_B > 0`.
3. **Discrete-Time Structure-Preserving GENERIC Integrator (Slides 189–190)**: for arbitrary time
   step `Δt ≥ 0` and exact discrete gradients `dE, dS`, `z' - z = Δt (L dE + M dS)` preserves energy
   exactly (`E z' = E z`) and increases entropy monotonically (`S z ≤ S z'`), extending by
   induction to multi-step neural rollouts `E (z N) = E (z 0)` and `S (z 0) ≤ S (z N)`.
4. **Souriau 1-Cocycle Affine Coadjoint Action & 2-Cocycle Affine Lie–Poisson Foliation**:
   `Ad♯_g(ξ) = Ad*_g(ξ) + θ(g)` forms a genuine group action on `g*`, and Casimir functions on
   the affine Lie–Poisson leaves have vanishing reversible derivative (`{C, H}_Θ = 0`), forcing
   irreversible dissipation to act transversely to symplectic coadjoint leaves.
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace InfoGeometry.Canonical.BarbarescoTINNDiscreteGENERICFoliation

/-! ### Part 1: Continuous & Discrete-Time GENERIC / Metriplectic Dynamics -/

/-- GENERIC / metriplectic velocity field `L ∇E + M ∇S`. -/
def genericVelocity {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℝ)
    (gradE gradS : Fin n → ℝ) : Fin n → ℝ :=
  L.mulVec gradE + M.mulVec gradS

/-- Any skew-symmetric matrix `Lᵀ = -L` has vanishing Rayleigh quotient `v ⋅ (L v) = 0`. -/
theorem skew_dotProduct_mulVec_self {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (hSkew : Lᵀ = -L) (v : Fin n → ℝ) :
    dotProduct v (L.mulVec v) = 0 := by
  have h1 : dotProduct v (L.mulVec v) = dotProduct (Lᵀ.mulVec v) v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have h2 : dotProduct (Lᵀ.mulVec v) v = -dotProduct (L.mulVec v) v := by
    rw [hSkew, Matrix.neg_mulVec, neg_dotProduct]
  have hcomm : dotProduct (L.mulVec v) v = dotProduct v (L.mulVec v) := dotProduct_comm _ _
  linarith [h1, h2, hcomm]

/-- Continuous First Law of Thermodynamics for GENERIC dynamics: `∇E ⋅ (L ∇E + M ∇S) = 0`. -/
theorem generic_continuous_first_law {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℝ)
    (gradE gradS : Fin n → ℝ)
    (hSkew : Lᵀ = -L) (hDegenE : M.mulVec gradE = 0)
    (hSymM : Mᵀ = M) :
    dotProduct gradE (genericVelocity L M gradE gradS) = 0 := by
  unfold genericVelocity
  rw [dotProduct_add, skew_dotProduct_mulVec_self L hSkew gradE, zero_add]
  have hAdj : dotProduct gradE (M.mulVec gradS) = dotProduct (Mᵀ.mulVec gradE) gradS := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [hSymM, hDegenE, zero_dotProduct] at hAdj
  exact hAdj

/-- Continuous Second Law of Thermodynamics for GENERIC dynamics:
`∇S ⋅ (L ∇E + M ∇S) = ∇S ⋅ (M ∇S) ≥ 0`. -/
theorem generic_continuous_second_law {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℝ)
    (gradE gradS : Fin n → ℝ)
    (hSkew : Lᵀ = -L) (hDegenS : L.mulVec gradS = 0)
    (hPSD : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (M.mulVec v)) :
    dotProduct gradS (genericVelocity L M gradE gradS) = dotProduct gradS (M.mulVec gradS) ∧
    0 ≤ dotProduct gradS (genericVelocity L M gradE gradS) := by
  have hRev : dotProduct gradS (L.mulVec gradE) = 0 := by
    have hAdj : dotProduct gradS (L.mulVec gradE) = dotProduct (Lᵀ.mulVec gradS) gradE := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [hSkew, Matrix.neg_mulVec, neg_dotProduct, hDegenS, zero_dotProduct, neg_zero] at hAdj
    exact hAdj
  have hEq : dotProduct gradS (genericVelocity L M gradE gradS) =
      dotProduct gradS (M.mulVec gradS) := by
    unfold genericVelocity
    rw [dotProduct_add, hRev, zero_add]
  exact ⟨hEq, hEq ▸ hPSD gradS⟩

/-! ### Part 2: Fluctuation-Dissipation Factorization (Barbaresco Slide 188) -/

/-- Fluctuation-dissipation dissipation matrix `M = (1 / (2 k_B)) B Bᵀ`. -/
def fluctuationDissipationMatrix {n m : ℕ} (kB : ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / (2 * kB)) • (B * Bᵀ)

/-- The fluctuation-dissipation matrix `M = (1 / (2 k_B)) B Bᵀ` is automatically symmetric. -/
theorem fluctuationDissipationMatrix_symmetric {n m : ℕ} (kB : ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (fluctuationDissipationMatrix kB B)ᵀ = fluctuationDissipationMatrix kB B := by
  unfold fluctuationDissipationMatrix
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- For `k_B > 0`, `M = (1 / (2 k_B)) B Bᵀ` is positive semidefinite on every state vector `v`. -/
theorem fluctuationDissipationMatrix_psd {n m : ℕ} (kB : ℝ) (hkB : 0 < kB)
    (B : Matrix (Fin n) (Fin m) ℝ) (v : Fin n → ℝ) :
    0 ≤ dotProduct v ((fluctuationDissipationMatrix kB B).mulVec v) := by
  unfold fluctuationDissipationMatrix
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hsq : 0 ≤ dotProduct (Bᵀ.mulVec v) (Bᵀ.mulVec v) := by
    unfold dotProduct
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  exact mul_nonneg (one_div_nonneg.mpr (by linarith [hkB])) hsq

/-- Exact recovery `B Bᵀ = 2 k_B M` whenever `k_B ≠ 0`. -/
theorem fluctuationDissipation_identity {n m : ℕ} (kB : ℝ) (hkB : kB ≠ 0)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    B * Bᵀ = (2 * kB) • fluctuationDissipationMatrix kB B := by
  unfold fluctuationDissipationMatrix
  rw [smul_smul]
  have hmul : (2 * kB) * (1 / (2 * kB)) = 1 := by
    field_simp [hkB]
  rw [hmul, one_smul]

/-! ### Part 3: Discrete-Time Structure-Preserving GENERIC Integrator (TINN) -/

/-- **Discrete First Law of TINN / GENERIC Integrators**:
Any discrete step `z' - z = Δt • (L dE + M dS)` using an exact discrete energy gradient `dE`
(`E z' - E z = dE ⋅ (z' - z)`) conserves energy `E z' = E z` for EVERY step size `Δt : ℝ`. -/
theorem tinn_discrete_first_law {n : ℕ} (E : (Fin n → ℝ) → ℝ)
    (L M : Matrix (Fin n) (Fin n) ℝ) (z z' dE dS : Fin n → ℝ) (dt : ℝ)
    (hStep : z' - z = dt • genericVelocity L M dE dS)
    (hGradE : E z' - E z = dotProduct dE (z' - z))
    (hSkew : Lᵀ = -L) (hSymM : Mᵀ = M) (hDegenE : M.mulVec dE = 0) :
    E z' = E z := by
  have hZero : dotProduct dE (genericVelocity L M dE dS) = 0 :=
    generic_continuous_first_law L M dE dS hSkew hDegenE hSymM
  rw [hStep, dotProduct_smul, smul_eq_mul, hZero, mul_zero] at hGradE
  exact sub_eq_zero.mp hGradE

/-- Exact discrete entropy increment formula `S z' - S z = Δt * (dS ⋅ M dS)`. -/
theorem tinn_discrete_second_law_eq {n : ℕ} (S : (Fin n → ℝ) → ℝ)
    (L M : Matrix (Fin n) (Fin n) ℝ) (z z' dE dS : Fin n → ℝ) (dt : ℝ)
    (hStep : z' - z = dt • genericVelocity L M dE dS)
    (hGradS : S z' - S z = dotProduct dS (z' - z))
    (hSkew : Lᵀ = -L) (hDegenS : L.mulVec dS = 0)
    (hPSD : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (M.mulVec v)) :
    S z' - S z = dt * dotProduct dS (M.mulVec dS) := by
  have hEnt := (generic_continuous_second_law L M dE dS hSkew hDegenS hPSD).1
  rw [hStep, dotProduct_smul, smul_eq_mul, hEnt] at hGradS
  exact hGradS

/-- **Discrete Second Law of TINN / GENERIC Integrators**:
For any step size `Δt ≥ 0` and PSD `M`, entropy is monotonically non-decreasing: `S z ≤ S z'`. -/
theorem tinn_discrete_second_law_nonneg {n : ℕ} (S : (Fin n → ℝ) → ℝ)
    (L M : Matrix (Fin n) (Fin n) ℝ) (z z' dE dS : Fin n → ℝ) (dt : ℝ)
    (hdt : 0 ≤ dt)
    (hStep : z' - z = dt • genericVelocity L M dE dS)
    (hGradS : S z' - S z = dotProduct dS (z' - z))
    (hSkew : Lᵀ = -L) (hDegenS : L.mulVec dS = 0)
    (hPSD : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (M.mulVec v)) :
    S z ≤ S z' := by
  have hEq := tinn_discrete_second_law_eq S L M z z' dE dS dt hStep hGradS hSkew hDegenS hPSD
  have hNonneg : 0 ≤ dt * dotProduct dS (M.mulVec dS) := mul_nonneg hdt (hPSD dS)
  exact sub_nonneg.mp (hEq.symm ▸ hNonneg)

/-- **Multi-Step TINN Trajectory Energy Conservation**:
Across any finite rollout of `N` discrete GENERIC steps, total energy is strictly invariant. -/
theorem tinn_multistep_energy_conservation {n : ℕ} (E : (Fin n → ℝ) → ℝ)
    (z dE dS : ℕ → (Fin n → ℝ)) (L M : ℕ → Matrix (Fin n) (Fin n) ℝ) (dt : ℕ → ℝ)
    (N : ℕ)
    (hSteps : ∀ k < N, z (k + 1) - z k = dt k • genericVelocity (L k) (M k) (dE k) (dS k))
    (hGrads : ∀ k < N, E (z (k + 1)) - E (z k) = dotProduct (dE k) (z (k + 1) - z k))
    (hSkews : ∀ k < N, (L k)ᵀ = -(L k))
    (hSymMs : ∀ k < N, (M k)ᵀ = M k)
    (hDegens : ∀ k < N, (M k).mulVec (dE k) = 0) :
    E (z N) = E (z 0) := by
  induction N with
  | zero => rfl
  | succ m ih =>
      have hm : E (z m) = E (z 0) := ih
        (fun k hk => hSteps k (Nat.lt_succ_of_lt hk))
        (fun k hk => hGrads k (Nat.lt_succ_of_lt hk))
        (fun k hk => hSkews k (Nat.lt_succ_of_lt hk))
        (fun k hk => hSymMs k (Nat.lt_succ_of_lt hk))
        (fun k hk => hDegens k (Nat.lt_succ_of_lt hk))
      have hLast := tinn_discrete_first_law E (L m) (M m) (z m) (z (m + 1)) (dE m) (dS m) (dt m)
        (hSteps m (Nat.lt_succ_self m)) (hGrads m (Nat.lt_succ_self m))
        (hSkews m (Nat.lt_succ_self m)) (hSymMs m (Nat.lt_succ_self m))
        (hDegens m (Nat.lt_succ_self m))
      exact hLast.trans hm

/-- **Multi-Step TINN Trajectory Entropy Monotonicity**:
Across any finite rollout of `N` discrete GENERIC steps with `dt k ≥ 0`, `S (z 0) ≤ S (z N)`. -/
theorem tinn_multistep_entropy_monotonicity {n : ℕ} (S : (Fin n → ℝ) → ℝ)
    (z dE dS : ℕ → (Fin n → ℝ)) (L M : ℕ → Matrix (Fin n) (Fin n) ℝ) (dt : ℕ → ℝ)
    (N : ℕ)
    (hdts : ∀ k < N, 0 ≤ dt k)
    (hSteps : ∀ k < N, z (k + 1) - z k = dt k • genericVelocity (L k) (M k) (dE k) (dS k))
    (hGrads : ∀ k < N, S (z (k + 1)) - S (z k) = dotProduct (dS k) (z (k + 1) - z k))
    (hSkews : ∀ k < N, (L k)ᵀ = -(L k))
    (hDegens : ∀ k < N, (L k).mulVec (dS k) = 0)
    (hPSDs : ∀ k < N, ∀ v : Fin n → ℝ, 0 ≤ dotProduct v ((M k).mulVec v)) :
    S (z 0) ≤ S (z N) := by
  induction N with
  | zero => exact le_rfl
  | succ m ih =>
      have hm : S (z 0) ≤ S (z m) := ih
        (fun k hk => hdts k (Nat.lt_succ_of_lt hk))
        (fun k hk => hSteps k (Nat.lt_succ_of_lt hk))
        (fun k hk => hGrads k (Nat.lt_succ_of_lt hk))
        (fun k hk => hSkews k (Nat.lt_succ_of_lt hk))
        (fun k hk => hDegens k (Nat.lt_succ_of_lt hk))
        (fun k hk => hPSDs k (Nat.lt_succ_of_lt hk))
      have hLast := tinn_discrete_second_law_nonneg S (L m) (M m) (z m) (z (m + 1)) (dE m) (dS m)
        (dt m) (hdts m (Nat.lt_succ_self m)) (hSteps m (Nat.lt_succ_self m))
        (hGrads m (Nat.lt_succ_self m)) (hSkews m (Nat.lt_succ_self m))
        (hDegens m (Nat.lt_succ_self m)) (hPSDs m (Nat.lt_succ_self m))
      exact le_trans hm hLast

/-- Explicit non-commutativity witness for concrete `2 × 2` real GENERIC operators. -/
def sampleSkew2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
def sampleSym2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

theorem sampleSkew2_sampleSym2_noncomm : sampleSkew2 * sampleSym2 ≠ sampleSym2 * sampleSkew2 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [sampleSkew2, sampleSym2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ### Part 4: Souriau 1-Cocycle Affine Coadjoint Action & Transverse Foliation (Slides 20, 51, 166) -/

/-- Souriau 1-cocycle at identity vanishes: `θ(1) = 0`. -/
theorem souriau_cocycle_one {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]
    (AdStar : G → V →ₗ[ℝ] V) (hOne : AdStar 1 = LinearMap.id)
    (θ : G → V) (hCocycle : ∀ g h : G, θ (g * h) = θ g + AdStar g (θ h)) :
    θ 1 = 0 := by
  have h := hCocycle 1 1
  rw [mul_one, hOne, LinearMap.id_apply] at h
  exact left_eq_add.mp h

/-- Souriau 1-cocycle inverse identity: `θ(g⁻¹) = -Ad*_{g⁻¹}(θ(g))`. -/
theorem souriau_cocycle_inv {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]
    (AdStar : G → V →ₗ[ℝ] V) (hOne : AdStar 1 = LinearMap.id)
    (θ : G → V) (hCocycle : ∀ g h : G, θ (g * h) = θ g + AdStar g (θ h)) (g : G) :
    θ g⁻¹ = -(AdStar g⁻¹ (θ g)) := by
  have h := hCocycle g⁻¹ g
  rw [inv_mul_cancel, souriau_cocycle_one AdStar hOne θ hCocycle] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Affine Souriau coadjoint action `Ad♯_g(ξ) = Ad*_g(ξ) + θ(g)` (Barbaresco Slide 51). -/
def affineCoadjointAction {G V : Type*} [AddCommGroup V] [Module ℝ V]
    (AdStar : G → V →ₗ[ℝ] V) (θ : G → V) (g : G) (ξ : V) : V :=
  AdStar g ξ + θ g

/-- Identity element acts trivially under the Souriau affine coadjoint action. -/
theorem affineCoadjointAction_one {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]
    (AdStar : G → V →ₗ[ℝ] V) (hOne : AdStar 1 = LinearMap.id)
    (θ : G → V) (hCocycle : ∀ g h : G, θ (g * h) = θ g + AdStar g (θ h)) (ξ : V) :
    affineCoadjointAction AdStar θ 1 ξ = ξ := by
  unfold affineCoadjointAction
  rw [hOne, LinearMap.id_apply, souriau_cocycle_one AdStar hOne θ hCocycle, add_zero]

/-- Multiplicative composition law for the Souriau affine coadjoint action on `g*`. -/
theorem affineCoadjointAction_mul {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]
    (AdStar : G → V →ₗ[ℝ] V) (hMul : ∀ g h : G, AdStar (g * h) = (AdStar g).comp (AdStar h))
    (θ : G → V) (hCocycle : ∀ g h : G, θ (g * h) = θ g + AdStar g (θ h)) (g h : G) (ξ : V) :
    affineCoadjointAction AdStar θ (g * h) ξ =
      affineCoadjointAction AdStar θ g (affineCoadjointAction AdStar θ h ξ) := by
  unfold affineCoadjointAction
  rw [hMul g h, LinearMap.comp_apply, map_add, hCocycle g h]
  abel

/-- Souriau 2-cocycle affine Lie–Poisson bracket on `g*` (`{X, Y}_Θ(μ) = μ ⁅X, Y⁆ + Θ X Y`,
Barbaresco Slide 166 & 170). -/
def affineLiePoissonBracket {g : Type*} [LieRing g] [Module ℝ g]
    (μ : g →ₗ[ℝ] ℝ) (Θ : g → g → ℝ) (X Y : g) : ℝ :=
  μ ⁅X, Y⁆ + Θ X Y

/-- Antisymmetry of the Souriau affine Lie–Poisson bracket for any skew 2-cocycle `Θ`. -/
theorem affineLiePoissonBracket_antisymm {g : Type*} [LieRing g] [Module ℝ g]
    (μ : g →ₗ[ℝ] ℝ) (Θ : g → g → ℝ) (hTheta : ∀ X Y : g, Θ X Y = -Θ Y X) (X Y : g) :
    affineLiePoissonBracket μ Θ X Y = -affineLiePoissonBracket μ Θ Y X := by
  unfold affineLiePoissonBracket
  rw [← lie_skew X Y, map_neg, hTheta X Y]
  ring

/-- Vanishing on identical gradients: `{X, X}_Θ(μ) = 0`. -/
theorem affineLiePoissonBracket_self {g : Type*} [LieRing g] [Module ℝ g]
    (μ : g →ₗ[ℝ] ℝ) (Θ : g → g → ℝ) (hTheta : ∀ X Y : g, Θ X Y = -Θ Y X) (X : g) :
    affineLiePoissonBracket μ Θ X X = 0 := by
  have h := affineLiePoissonBracket_antisymm μ Θ hTheta X X
  linarith [h]

/-- **Casimir Leaf Invariance Transverse to Symplectic Leaves (Barbaresco Slides 20 & 170)**:
Every Casimir gradient `X_C` has zero reversible derivative `{X_C, X_H}_Θ(μ) = 0` for any
Hamiltonian gradient `X_H`, so entropy as a Casimir can vary only transversely via the metric bracket `M`. -/
theorem casimir_vanishes_along_hamiltonian {g : Type*} [LieRing g] [Module ℝ g]
    (μ : g →ₗ[ℝ] ℝ) (Θ : g → g → ℝ) (X_C X_H : g)
    (hCasimir : ∀ Y : g, affineLiePoissonBracket μ Θ X_C Y = 0) :
    affineLiePoissonBracket μ Θ X_C X_H = 0 :=
  hCasimir X_H

end InfoGeometry.Canonical.BarbarescoTINNDiscreteGENERICFoliation
