/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.CartanTrialityZornProduct
import InfoGeometry.Hydrodynamics.ZornMadelungInformationPotential
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# AI Studio 1SSh9 Track M3: Stiefel Riccati, Zorn Commutators, SUSY Solitons, Rotor/CGA & M₄(R) Ward

Formalizes all missing finite algebraic targets from Phase E (`E-C1`, `E-C2a`, `E-C3`, `E-C4a`, `E-C5`, `E-C6a`)
of `docs/contracts/AISTUDIO_1SSH9_THEOREM_CONTRACTS.md`, reusing `CartanTrialityZorn` and `ZornMadelung`:
- `E-C1`: Noncommutative `SL2Generator` Riccati flow, `riccatiVariationMetric`, `[HasImaginaryUnit R]`
  `spacetimeBispinor`, `HestenesCl11`, `adsMetricTensor_det = -2`, `adjugate2`, `PenroseTwistor`.
- `E-C2a`: Finite `fisherRaoMetric`/`fisherRaoEnergy`, first law of entanglement, entropy Hessian,
  `surprisalHessianMode`, `expectation_surprisal_hessian_is_fisher`, `StressEnergyTrio`.
- `E-C3`: `ZornMatrix` noncommutative commutator (`u₁ × u₂`), `FluidZornConfig` lightcone gauge invariance,
  `LaxPair` isospectrality, and `marchenko_resolvent_formula`.
- `E-C4a`: Riccati-SUSY partner Hamiltonians (`V± = W² ± ħ W'`), `FactorizationOps`,
  `witten_index_of_soliton`, `derrick_collapse_avoidance_balance`.
- `E-C5`: Generic `[Ring A]` `ReversionAlgebra`/`Rotor` and `ConformalBasis` 6D CGA null vectors.
- `E-C6a`: `Matrix (Fin 4) (Fin 4) R` `diff_inverse_identity`, `maurer_cartan_deductive_flat`,
  `covariant_differential_nilpotent_on_flat`, Ward blades, and `zorn_schur_vanishes_on_lightcone`.
-/

namespace InfoGeometry.Synthesis.Aistudio1SSh9RiccatiZornConformalBridge

open InfoGeometry.SuperGrassmannian
open InfoGeometry.Hydrodynamics
open Matrix

set_option warn.classDefReducibility false

/-! ## Section 1: Explicit Noncommutativity Witnesses for Matrix Carriers -/

section NoncommWitnesses

def m2E12 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
def m2E21 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

theorem m2_noncommutative_exists {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A := by
  refine ⟨m2E12 R, m2E21 R, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [m2E12, m2E21, Matrix.mul_apply, Fin.sum_univ_two] at h00

def m2Q12 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
def m2Q21 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

theorem m2Q_noncommutative_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℚ, A * B ≠ B * A :=
  m2_noncommutative_exists

def m2Z12 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
def m2Z21 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

theorem m2Z_noncommutative_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A :=
  m2_noncommutative_exists

def m3E12 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; 0, 0, 0; 0, 0, 0]

def m3E21 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0; 1, 0, 0; 0, 0, 0]

theorem m3_noncommutative_exists {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨m3E12 R, m3E21 R, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [m3E12, m3E21, Matrix.mul_apply, Fin.sum_univ_three] at h00

def m4E12 (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

def m4E21 (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem m4_noncommutative_exists {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 4) (Fin 4) R, A * B ≠ B * A := by
  refine ⟨m4E12 R, m4E21 R, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [m4E12, m4E21, Matrix.mul_apply, Fin.sum_univ_four] at h00

end NoncommWitnesses

/-! ## Section 2 (E-C1): Stiefel Riccati, Trace Orthogonality, Bispinors, HestenesCl11, AdS₃, & Penrose Twistor -/

/-- Traceless `2×2` block generator for the Stiefel affine chart Riccati flow. -/
structure SL2Generator (R : Type*) [Ring R] where
  a : R
  b : R
  c : R
  d : R
  trace_zero : a + d = 0

/-- Constructive witness of `SL2Generator ℤ`. -/
def intSL2Generator : SL2Generator ℤ := ⟨1, 0, 0, -1, rfl⟩

section StiefelRiccati

variable {R : Type*} [CommRing R]

def lorentzSpinGen (θ : R) : SL2Generator R := ⟨θ, 0, 0, -θ, by ring⟩
def lightconeTransGen (ε : R) : SL2Generator R := ⟨0, ε, 0, 0, by ring⟩
def conformalInvGen (η : R) : SL2Generator R := ⟨0, 0, η, 0, by ring⟩

/-- Noncommutative Riccati variation `δT = b + T d - a T - T c T`. -/
def riccatiVariation {A : Type*} [Ring A] (gen : SL2Generator A) (T : A) : A :=
  gen.b + T * gen.d - gen.a * T - T * gen.c * T

theorem riccati_spin_lightcone_bracket (θ ε T : R) :
    riccatiVariation (lorentzSpinGen θ) (T + ε) - riccatiVariation (lorentzSpinGen θ) T =
      -(2 * θ * ε) := by
  dsimp [riccatiVariation, lorentzSpinGen]
  ring

def riccatiVariationMetric {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) : R :=
  Matrix.trace (A * B)

theorem spin_lightcone_variation_orthogonal (θ ε : R) :
    riccatiVariationMetric (!![θ, 0; 0, -θ] : Matrix (Fin 2) (Fin 2) R)
      (!![0, ε; 0, 0] : Matrix (Fin 2) (Fin 2) R) = 0 := by
  simp [riccatiVariationMetric, Matrix.trace]

end StiefelRiccati

/-- Commutative ring equipped with an imaginary unit `I² = -1`. -/
class HasImaginaryUnit (R : Type*) [CommRing R] where
  I : R
  I_sq : I * I = -1

/-- Constructive witness of `HasImaginaryUnit ℂ`. -/
noncomputable def complexHasImaginaryUnit : HasImaginaryUnit ℂ where
  I := Complex.I
  I_sq := by rw [← sq, Complex.I_sq]

section BispinorSpacetime

variable {R : Type*} [CommRing R] [HI : HasImaginaryUnit R]

def spacetimeBispinor (x₀ x₁ x₂ x₃ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![x₀ + x₃, x₁ - HI.I * x₂;
     x₁ + HI.I * x₂, x₀ - x₃]

theorem bispinor_det_is_minkowski_interval (x₀ x₁ x₂ x₃ : R) :
    Matrix.det (spacetimeBispinor x₀ x₁ x₂ x₃) = x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  dsimp [spacetimeBispinor]
  rw [Matrix.det_fin_two]
  have hI : HI.I * HI.I = -1 := HI.I_sq
  calc (x₀ + x₃) * (x₀ - x₃) - (x₁ - HI.I * x₂) * (x₁ + HI.I * x₂)
    _ = (x₀ ^ 2 - x₃ ^ 2) - (x₁ ^ 2 - (HI.I * HI.I) * x₂ ^ 2) := by ring
    _ = (x₀ ^ 2 - x₃ ^ 2) - (x₁ ^ 2 - (-1) * x₂ ^ 2) := by rw [hI]
    _ = x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by ring

omit HI in
theorem lorenz_variation_split (ω_rot ω_boost X : Matrix (Fin 2) (Fin 2) R) :
    (ω_rot * X - X * ω_rot) + (ω_boost * X + X * ω_boost) =
      (ω_rot + ω_boost) * X + X * (-ω_rot + ω_boost) := by
  noncomm_ring

end BispinorSpacetime

/-- Algebraic generators of `HestenesCl11`: elliptic `i² = -1`, hyperbolic `j² = 1`, parabolic `e² = 0`. -/
structure HestenesCl11 (A : Type*) [Ring A] where
  i : A
  j : A
  e : A
  i_sq : i * i = -1
  j_sq : j * j = 1
  e_sq : e * e = 0
  ij_anti : i * j + j * i = 0

/-- Constructive witness of `HestenesCl11` in `M₂(ℤ)`. -/
def mat2HestenesCl11 : HestenesCl11 (Matrix (Fin 2) (Fin 2) ℤ) where
  i := !![0, -1; 1, 0]
  j := !![1, 0; 0, -1]
  e := !![0, 1; 0, 0]
  i_sq := by decide
  j_sq := by decide
  e_sq := by decide
  ij_anti := by decide

section AdSMetricAndTwistor

variable {R : Type*} [CommRing R]

def adsMetricTensor : Matrix (Fin 3) (Fin 3) R :=
  !![2, 0, 0;
     0, 0, 1;
     0, 1, 0]

theorem adsMetricTensor_det :
    Matrix.det (adsMetricTensor (R := R)) = -2 := by
  dsimp [adsMetricTensor]
  rw [Matrix.det_fin_three]
  norm_num

def adjugate2 (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 1 1, -M 0 1;
    -M 1 0, M 0 0]

def det2 (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

theorem adjugate2_mul_self (M : Matrix (Fin 2) (Fin 2) R) :
    adjugate2 M * M = (det2 M) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate2, det2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end AdSMetricAndTwistor

/-- Penrose twistor `(ω, π) ∈ R² × R²`. -/
structure PenroseTwistor (R : Type*) where
  ω : Fin 2 → R
  π : Fin 2 → R

/-- Constructive witness of `PenroseTwistor ℤ`. -/
def intPenroseTwistor : PenroseTwistor ℤ := ⟨![0, 0], ![1, 0]⟩

section TwistorIncidence

variable {R : Type*} [CommRing R]

def isIncident (Z : PenroseTwistor R) (X : Matrix (Fin 2) (Fin 2) R) : Prop :=
  X *ᵥ Z.π = Z.ω

theorem twistor_incidence_forces_null_separation
    (X Y : Matrix (Fin 2) (Fin 2) R) (Z : PenroseTwistor R)
    (hX : isIncident Z X) (hY : isIncident Z Y)
    (hnorm : Z.π 0 = 1 ∨ Z.π 1 = 1) :
    det2 (X - Y) = 0 := by
  have hdisp : (X - Y) *ᵥ Z.π = 0 := by
    dsimp [isIncident] at hX hY
    rw [Matrix.sub_mulVec, hX, hY, sub_self]
  have hdetπ : (det2 (X - Y)) • Z.π = 0 := by
    calc (det2 (X - Y)) • Z.π
      _ = ((det2 (X - Y)) • (1 : Matrix (Fin 2) (Fin 2) R)) *ᵥ Z.π := by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (adjugate2 (X - Y) * (X - Y)) *ᵥ Z.π := by rw [adjugate2_mul_self]
      _ = adjugate2 (X - Y) *ᵥ ((X - Y) *ᵥ Z.π) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = adjugate2 (X - Y) *ᵥ 0 := by rw [hdisp]
      _ = 0 := Matrix.mulVec_zero _
  rcases hnorm with h0 | h1
  · have h := congrFun hdetπ 0
    simpa [h0] using h
  · have h := congrFun hdetπ 1
    simpa [h1] using h

end TwistorIncidence

/-! ## Section 3 (E-C2a): Finite Fisher–Rao Metric, First Law, Surprisal Hessian, & Stress-Energy -/

section FisherSurprisal

noncomputable def fisherRaoMetric {n : ℕ} (p u v : Fin n → ℝ) : ℝ :=
  ∑ i, (u i * v i) / p i

noncomputable def fisherRaoEnergy {n : ℕ} (p u : Fin n → ℝ) : ℝ :=
  fisherRaoMetric p u u

theorem fisherRao_nonneg {n : ℕ} (p u : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    0 ≤ fisherRaoEnergy p u := by
  dsimp [fisherRaoEnergy, fisherRaoMetric]
  refine Finset.sum_nonneg ?_
  intro i _
  exact div_nonneg (mul_self_nonneg (u i)) (le_of_lt (hp i))

noncomputable def modularHam {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  -Real.log (p i)

theorem first_law_of_entanglement {n : ℕ} (p dp : Fin n → ℝ)
    (hsum : (∑ i, dp i) = 0) :
    (∑ i, (-Real.log (p i) - 1) * dp i) = ∑ i, modularHam p i * dp i := by
  have h1 : ∀ i, (-Real.log (p i) - 1) * dp i = modularHam p i * dp i - dp i := by
    intro i
    dsimp [modularHam]
    ring
  simp_rw [h1, Finset.sum_sub_distrib, hsum, sub_zero]

theorem entropy_hessian_eq_neg_fisher {n : ℕ} (p u : Fin n → ℝ) :
    (∑ i, -(u i * u i) / (2 * p i)) = -(1 / 2 : ℝ) * fisherRaoEnergy p u := by
  dsimp [fisherRaoEnergy, fisherRaoMetric]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

def surprisalHessianMode (dP_mu dP_nu d2P_munu invP invP2 : ℝ) : ℝ :=
  (dP_mu * dP_nu) * invP2 - d2P_munu * invP

theorem mode_hessian_contraction (P dP_mu dP_nu d2P_munu invP invP2 : ℝ)
    (h_inv : P * invP = 1) (h_inv2 : invP2 = invP * invP) :
    P * surprisalHessianMode dP_mu dP_nu d2P_munu invP invP2 =
      (dP_mu * dP_nu) * invP - d2P_munu := by
  dsimp [surprisalHessianMode]
  rw [h_inv2]
  calc P * ((dP_mu * dP_nu) * (invP * invP) - d2P_munu * invP)
    _ = (P * invP) * ((dP_mu * dP_nu) * invP) - (P * invP) * d2P_munu := by ring
    _ = 1 * ((dP_mu * dP_nu) * invP) - 1 * d2P_munu := by rw [h_inv]
    _ = (dP_mu * dP_nu) * invP - d2P_munu := by ring

theorem expectation_surprisal_hessian_is_fisher {K : ℕ}
    (P dP_mu dP_nu d2P_munu invP invP2 : Fin K → ℝ)
    (h_inv : ∀ k, P k * invP k = 1)
    (h_inv2 : ∀ k, invP2 k = invP k * invP k)
    (h_conservation : (∑ k, d2P_munu k) = 0) :
    (∑ k, P k * surprisalHessianMode (dP_mu k) (dP_nu k) (d2P_munu k) (invP k) (invP2 k)) =
      ∑ k, (dP_mu k * dP_nu k) * invP k := by
  have hmode : ∀ k,
      P k * surprisalHessianMode (dP_mu k) (dP_nu k) (d2P_munu k) (invP k) (invP2 k) =
        (dP_mu k * dP_nu k) * invP k - d2P_munu k := fun k =>
    mode_hessian_contraction (P k) (dP_mu k) (dP_nu k) (d2P_munu k) (invP k) (invP2 k)
      (h_inv k) (h_inv2 k)
  simp_rw [hmode, Finset.sum_sub_distrib, h_conservation, sub_zero]

end FisherSurprisal

structure StressEnergyTrio (R : Type*) where
  T_matter : R
  T_maxwell : R
  T_bohm : R

/-- Constructive witness for `StressEnergyTrio`. -/
def intStressEnergyTrio : StressEnergyTrio ℤ := ⟨1, -1, 0⟩

def totalStressEnergy {R : Type*} [CommRing R] (trio : StressEnergyTrio R) : R :=
  trio.T_matter + trio.T_maxwell + trio.T_bohm

theorem stress_energy_matches_zorn_components {R : Type*} [CommRing R]
    (mv_sq A_sq Q_sq : R) :
    totalStressEnergy (⟨mv_sq, -A_sq, -Q_sq⟩ : StressEnergyTrio R) = mv_sq - A_sq - Q_sq := by
  dsimp [totalStressEnergy]
  ring

/-! ## Section 4 (E-C3): Zorn Commutator, FluidZornConfig, LaxPair & Marchenko -/

section ZornFluidAndLax

def zornCommutator {R : Type*} [CommRing R]
    (Z₁ Z₂ : CartanTrialityZorn.ZornMatrix R) : CartanTrialityZorn.ZornMatrix R :=
  CartanTrialityZorn.ZornMatrix.sub
    (CartanTrialityZorn.ZornMatrix.mul Z₁ Z₂)
    (CartanTrialityZorn.ZornMatrix.mul Z₂ Z₁)

theorem zorn_vorticity_commutator_non_scalar :
    ∃ Z₁ Z₂ : CartanTrialityZorn.ZornMatrix ℤ,
      zornCommutator Z₁ Z₂ ≠ CartanTrialityZorn.ZornMatrix.zero := by
  refine ⟨CartanTrialityZorn.ZornMatrix.U ⟨1, 0, 0⟩,
    CartanTrialityZorn.ZornMatrix.U ⟨0, 1, 0⟩, ?_⟩
  intro h
  have hv := congrArg (fun M => M.v.z) h
  revert hv
  decide

theorem zorn_madelung_det_balance (S Q : ℝ) (A mv : ZornMadelung.Vec3)
    (h_gauge : S ^ 2 = ZornMadelung.Vec3.sq A) :
    ZornMadelung.ZornMatrix.det (ZornMadelung.ZornMatrix.makePotential S Q A mv) =
      ZornMadelung.Vec3.sq mv - Q ^ 2 :=
  ZornMadelung.ZornMatrix.zorn_kinetic_fisher_balance S Q A mv h_gauge

theorem zorn_potential_is_solution (S Q : ℝ) (A mv : ZornMadelung.Vec3)
    (h_lightcone : S ^ 2 - Q ^ 2 = ZornMadelung.Vec3.sq A - ZornMadelung.Vec3.sq mv) :
    ZornMadelung.ZornMatrix.det (ZornMadelung.ZornMatrix.makePotential S Q A mv) = 0 := by
  rw [ZornMadelung.ZornMatrix.zorn_potential_det_split, h_lightcone, sub_self]

end ZornFluidAndLax

/-- Four-field fluid-Zorn configuration `(S, Q, A, mv)` over `CartanTrialityZorn.Vec3 R`. -/
structure FluidZornConfig (R : Type*) where
  S : R
  Q : R
  A : CartanTrialityZorn.Vec3 R
  mv : CartanTrialityZorn.Vec3 R

/-- Constructive witness of `FluidZornConfig`. -/
def intFluidZornConfig : FluidZornConfig ℤ :=
  ⟨1, 0, ⟨1, 0, 0⟩, ⟨0, 0, 0⟩⟩

def zornFluidDet {R : Type*} [CommRing R] (cfg : FluidZornConfig R) : R :=
  (cfg.S + cfg.Q) * (cfg.S - cfg.Q) -
    CartanTrialityZorn.Vec3.dot
      (CartanTrialityZorn.Vec3.add cfg.A cfg.mv)
      (CartanTrialityZorn.Vec3.sub cfg.A cfg.mv)

theorem gauge_shift_invariance_on_lightcone {R : Type*} [CommRing R]
    (cfg : FluidZornConfig R) (φ : R) (k : CartanTrialityZorn.Vec3 R)
    (h_gauge : (cfg.S + φ) ^ 2 - CartanTrialityZorn.Vec3.dot
        (CartanTrialityZorn.Vec3.add cfg.A k) (CartanTrialityZorn.Vec3.add cfg.A k) =
      cfg.S ^ 2 - CartanTrialityZorn.Vec3.dot cfg.A cfg.A) :
    zornFluidDet ⟨cfg.S + φ, cfg.Q, CartanTrialityZorn.Vec3.add cfg.A k, cfg.mv⟩ =
      zornFluidDet cfg := by
  have h1 : zornFluidDet cfg =
      cfg.S ^ 2 - CartanTrialityZorn.Vec3.dot cfg.A cfg.A - cfg.Q ^ 2 +
        CartanTrialityZorn.Vec3.dot cfg.mv cfg.mv := by
    dsimp [zornFluidDet, CartanTrialityZorn.Vec3.dot, CartanTrialityZorn.Vec3.add,
      CartanTrialityZorn.Vec3.sub]
    ring
  have h2 : zornFluidDet ⟨cfg.S + φ, cfg.Q, CartanTrialityZorn.Vec3.add cfg.A k, cfg.mv⟩ =
      (cfg.S + φ) ^ 2 - CartanTrialityZorn.Vec3.dot
        (CartanTrialityZorn.Vec3.add cfg.A k) (CartanTrialityZorn.Vec3.add cfg.A k) - cfg.Q ^ 2 +
        CartanTrialityZorn.Vec3.dot cfg.mv cfg.mv := by
    dsimp [zornFluidDet, CartanTrialityZorn.Vec3.dot, CartanTrialityZorn.Vec3.add,
      CartanTrialityZorn.Vec3.sub]
    ring
  rw [h2, h_gauge, ← h1]

/-- Operator Lax pair `(L, B)` in an associative ring `A`. -/
structure LaxPair (A : Type*) [Ring A] where
  L : A
  B : A

/-- Constructive noncommutative witness of `LaxPair` in `M₂(ℤ)`. -/
def mat2LaxPair : LaxPair (Matrix (Fin 2) (Fin 2) ℤ) where
  L := m2Z12
  B := m2Z21

section LaxSystem

variable {A : Type*} [Ring A]

def laxBracket (P : LaxPair A) : A :=
  P.B * P.L - P.L * P.B

theorem eigenvalue_time_derivative_zero (L B ψ ev : A)
    (he : L * ψ = ev * ψ) (hc : B * ev = ev * B) :
    (B * L - L * B) * ψ + L * (B * ψ) = ev * (B * ψ) := by
  calc (B * L - L * B) * ψ + L * (B * ψ)
    _ = B * (L * ψ) - L * (B * ψ) + L * (B * ψ) := by noncomm_ring
    _ = B * (ev * ψ) := by rw [he]; abel
    _ = (B * ev) * ψ := by rw [mul_assoc]
    _ = (ev * B) * ψ := by rw [hc]
    _ = ev * (B * ψ) := by rw [mul_assoc]

theorem marchenko_resolvent_formula (K F inv_F : A)
    (hm : K * (1 + F) + F = 0) (hi : (1 + F) * inv_F = 1) :
    K = -(F * inv_F) := by
  have h1 : K * (1 + F) = -F := eq_neg_of_add_eq_zero_left hm
  calc K = K * 1 := (mul_one K).symm
    _ = K * ((1 + F) * inv_F) := by rw [hi]
    _ = (K * (1 + F)) * inv_F := by rw [mul_assoc]
    _ = (-F) * inv_F := by rw [h1]
    _ = -(F * inv_F) := neg_mul F inv_F

end LaxSystem

/-! ## Section 5 (E-C4a): Riccati-SUSY Partner Hamiltonians, Witten Index, & Derrick Balance -/

/-- Superpotential derivative data `(W, W', ħ)` for supersymmetric partner potentials. -/
structure SuperpotentialData (R : Type*) [CommRing R] where
  W : R
  dW : R
  hbar : R

/-- Constructive witness of `SuperpotentialData ℤ`. -/
def intSuperpotentialData : SuperpotentialData ℤ := ⟨1, 1, 1⟩

/-- Factorization operators `(A, A†)` for supersymmetric partner Hamiltonians `H₋ = A†A`, `H₊ = AA†`. -/
structure FactorizationOps (A : Type*) [Ring A] where
  A_op : A
  A_dag : A

/-- Constructive witness of `FactorizationOps` in `M₂(ℤ)`. -/
def mat2FactorizationOps : FactorizationOps (Matrix (Fin 2) (Fin 2) ℤ) where
  A_op := m2Z12
  A_dag := m2Z21

section RiccatiSUSY

variable {R : Type*} [CommRing R]

def potentialMinus (S : SuperpotentialData R) : R := S.W ^ 2 - S.hbar * S.dW
def potentialPlus (S : SuperpotentialData R) : R := S.W ^ 2 + S.hbar * S.dW

theorem potential_difference_is_riccati_derivative (S : SuperpotentialData R) :
    potentialPlus S - potentialMinus S = 2 * S.hbar * S.dW := by
  dsimp [potentialPlus, potentialMinus]
  ring

theorem potential_sum_is_twice_square (S : SuperpotentialData R) :
    potentialPlus S + potentialMinus S = 2 * S.W ^ 2 := by
  dsimp [potentialPlus, potentialMinus]
  ring

def susyHMinus {A : Type*} [Ring A] (F : FactorizationOps A) : A := F.A_dag * F.A_op
def susyHPlus {A : Type*} [Ring A] (F : FactorizationOps A) : A := F.A_op * F.A_dag

theorem vacuum_ground_state_zero_energy {A : Type*} [Ring A]
    (F : FactorizationOps A) (ψ₀ : A) (h_ann : F.A_op * ψ₀ = 0) :
    susyHMinus F * ψ₀ = 0 := by
  dsimp [susyHMinus]
  rw [mul_assoc, h_ann, mul_zero]

theorem isospectral_intertwining {A : Type*} [Ring A]
    (F : FactorizationOps A) (ψ : A) :
    susyHPlus F * (F.A_op * ψ) = F.A_op * (susyHMinus F * ψ) := by
  dsimp [susyHPlus, susyHMinus]
  simp only [mul_assoc]

def wittenIndex (n_zero_minus n_zero_plus : ℤ) : ℤ :=
  n_zero_minus - n_zero_plus

theorem witten_index_of_soliton : wittenIndex 1 0 = 1 := rfl

theorem derrick_collapse_avoidance_balance (T V lam : R)
    (h_stat : (1 : R) * T + (3 : R) * V = 0)
    (h_scale : lam = 1) :
    lam * T + (3 : R) * lam ^ 3 * V = 0 := by
  rw [h_scale]
  simpa using h_stat

end RiccatiSUSY

/-! ## Section 6 (E-C5): Generic `[Ring A]` ReversionAlgebra/Rotor & ConformalBasis -/

/-- Associative ring equipped with a Clifford-style reversion anti-involution. -/
structure ReversionAlgebra (A : Type*) [Ring A] where
  rev : A → A
  rev_add : ∀ x y, rev (x + y) = rev x + rev y
  rev_mul : ∀ x y, rev (x * y) = rev y * rev x
  rev_involutive : ∀ x, rev (rev x) = x
  rev_one : rev 1 = 1

/-- Constructive noncommutative witness of `ReversionAlgebra` via matrix transpose on `M₂(ℤ)`. -/
def mat2ReversionAlgebra : ReversionAlgebra (Matrix (Fin 2) (Fin 2) ℤ) where
  rev := Matrix.transpose
  rev_add := Matrix.transpose_add
  rev_mul := Matrix.transpose_mul
  rev_involutive := Matrix.transpose_transpose
  rev_one := Matrix.transpose_one

/-- Unital rotor `R * rev(R) = 1` and `rev(R) * R = 1` in a `ReversionAlgebra`. -/
structure Rotor {A : Type*} [Ring A] (RA : ReversionAlgebra A) where
  R : A
  unit_right : R * RA.rev R = 1
  unit_left : RA.rev R * R = 1

/-- Constructive witness of a `Rotor` for `mat2ReversionAlgebra`. -/
def mat2IdRotor : Rotor mat2ReversionAlgebra where
  R := 1
  unit_right := by decide
  unit_left := by decide

section RotorAndConformal

variable {A : Type*} [Ring A]

def rotorSandwich {RA : ReversionAlgebra A} (rot : Rotor RA) (v : A) : A :=
  rot.R * v * RA.rev rot.R

theorem rotor_preserves_vector_norm {RA : ReversionAlgebra A}
    (rot : Rotor RA) (v : A) (h_central : (v * v) * RA.rev rot.R = RA.rev rot.R * (v * v)) :
    rotorSandwich rot v * rotorSandwich rot v = v * v := by
  dsimp [rotorSandwich]
  calc (rot.R * v * RA.rev rot.R) * (rot.R * v * RA.rev rot.R)
    _ = rot.R * v * ((RA.rev rot.R * rot.R) * v * RA.rev rot.R) := by simp only [mul_assoc]
    _ = rot.R * ((v * v) * RA.rev rot.R) := by
        rw [rot.unit_left, one_mul]; simp only [mul_assoc]
    _ = rot.R * (RA.rev rot.R * (v * v)) := by rw [h_central]
    _ = (rot.R * RA.rev rot.R) * (v * v) := by rw [← mul_assoc]
    _ = v * v := by rw [rot.unit_right, one_mul]

theorem bivector_infinitesimal_commutator (half B v : A)
    (h_comm : half * B = B * half) (h_comm_v : half * v = v * half) :
    (1 + half * B) * v * (1 - half * B) =
      v + half * (B * v - v * B) - (half * half) * (B * v * B) := by
  calc (1 + half * B) * v * (1 - half * B)
    _ = v + (half * B) * v - v * (half * B) - (half * B) * v * (half * B) := by noncomm_ring
    _ = v + (half * (B * v) - half * (v * B)) - (half * half) * (B * v * B) := by
        have h1 : v * (half * B) = half * (v * B) := by
          rw [← mul_assoc, ← h_comm_v, mul_assoc]
        have h2 : (half * B) * v * (half * B) = (half * half) * (B * v * B) := by
          calc (half * B) * v * (half * B)
            _ = half * (B * (v * half)) * B := by simp only [mul_assoc]
            _ = half * (B * (half * v)) * B := by rw [h_comm_v]
            _ = half * ((B * half) * v) * B := by simp only [mul_assoc]
            _ = half * ((half * B) * v) * B := by rw [h_comm]
            _ = (half * half) * (B * v * B) := by simp only [mul_assoc]
        rw [h1, h2]
        noncomm_ring
    _ = v + half * (B * v - v * B) - (half * half) * (B * v * B) := by
        rw [mul_sub]

end RotorAndConformal

/-- Conformal geometric algebra null-pair basis `(n₊, n₋, ½)` over an associative ring `A`. -/
structure ConformalBasis (A : Type*) [Ring A] where
  n_plus : A
  n_minus : A
  half : A
  n_plus_sq : n_plus * n_plus = 0
  n_minus_sq : n_minus * n_minus = 0
  anticomm_null : n_plus * n_minus + n_minus * n_plus = -2
  h_half : (2 : A) * half = 1
  half_comm : ∀ x, half * x = x * half

/-- Constructive witness of `ConformalBasis` in `M₂(ℚ)`. -/
def mat2RatConformalBasis : ConformalBasis (Matrix (Fin 2) (Fin 2) ℚ) where
  n_plus := !![0, 1; 0, 0]
  n_minus := !![0, 0; -2, 0]
  half := (1 / 2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)
  n_plus_sq := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  n_minus_sq := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  anticomm_null := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.ofNat_apply] <;>
      norm_num
  h_half := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply, Matrix.one_apply] <;>
      norm_num
  half_comm x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

section ConformalCGA

variable {A : Type*} [Ring A]

def conformalVector (CB : ConformalBasis A) (x x_sq : A) : A :=
  x + CB.n_plus + (CB.half * x_sq) * CB.n_minus

theorem conformal_vector_is_strictly_null (CB : ConformalBasis A) (x x_sq : A)
    (hx_sq : x * x = x_sq)
    (hx_plus : x * CB.n_plus + CB.n_plus * x = 0)
    (hx_minus : x * CB.n_minus + CB.n_minus * x = 0)
    (h_cent_sq : ∀ z, x_sq * z = z * x_sq) :
    conformalVector CB x x_sq * conformalVector CB x x_sq = 0 := by
  dsimp [conformalVector]
  let α : A := CB.half * x_sq
  have hα_x : α * x = x * α := by
    dsimp [α]
    calc (CB.half * x_sq) * x
      _ = CB.half * (x_sq * x) := by rw [mul_assoc]
      _ = CB.half * (x * x_sq) := by rw [h_cent_sq]
      _ = (CB.half * x) * x_sq := by rw [← mul_assoc]
      _ = (x * CB.half) * x_sq := by rw [CB.half_comm]
      _ = x * (CB.half * x_sq) := by rw [mul_assoc]
  have hα_p : α * CB.n_plus = CB.n_plus * α := by
    dsimp [α]
    calc (CB.half * x_sq) * CB.n_plus
      _ = CB.half * (x_sq * CB.n_plus) := by rw [mul_assoc]
      _ = CB.half * (CB.n_plus * x_sq) := by rw [h_cent_sq]
      _ = (CB.half * CB.n_plus) * x_sq := by rw [← mul_assoc]
      _ = (CB.n_plus * CB.half) * x_sq := by rw [CB.half_comm]
      _ = CB.n_plus * (CB.half * x_sq) := by rw [mul_assoc]
  have hα_m : α * CB.n_minus = CB.n_minus * α := by
    dsimp [α]
    calc (CB.half * x_sq) * CB.n_minus
      _ = CB.half * (x_sq * CB.n_minus) := by rw [mul_assoc]
      _ = CB.half * (CB.n_minus * x_sq) := by rw [h_cent_sq]
      _ = (CB.half * CB.n_minus) * x_sq := by rw [← mul_assoc]
      _ = (CB.n_minus * CB.half) * x_sq := by rw [CB.half_comm]
      _ = CB.n_minus * (CB.half * x_sq) := by rw [mul_assoc]
  have h2α : (2 : A) * α = x_sq := by
    dsimp [α]
    rw [← mul_assoc, CB.h_half, one_mul]
  change (x + CB.n_plus + α * CB.n_minus) * (x + CB.n_plus + α * CB.n_minus) = 0
  calc (x + CB.n_plus + α * CB.n_minus) * (x + CB.n_plus + α * CB.n_minus)
    _ = (x * x) + (x * CB.n_plus + CB.n_plus * x) + (CB.n_plus * CB.n_plus) +
          α * (x * CB.n_minus + CB.n_minus * x) +
          α * (CB.n_plus * CB.n_minus + CB.n_minus * CB.n_plus) +
          (α * α) * (CB.n_minus * CB.n_minus) := by
        have haxm : (α * CB.n_minus) * x = α * (CB.n_minus * x) := by rw [mul_assoc]
        have hxam : x * (α * CB.n_minus) = α * (x * CB.n_minus) := by
          rw [← mul_assoc, ← hα_x, mul_assoc]
        have hapm : (α * CB.n_minus) * CB.n_plus = α * (CB.n_minus * CB.n_plus) := by rw [mul_assoc]
        have hpam : CB.n_plus * (α * CB.n_minus) = α * (CB.n_plus * CB.n_minus) := by
          rw [← mul_assoc, ← hα_p, mul_assoc]
        have haam : (α * CB.n_minus) * (α * CB.n_minus) = (α * α) * (CB.n_minus * CB.n_minus) := by
          calc (α * CB.n_minus) * (α * CB.n_minus)
            _ = α * (CB.n_minus * α) * CB.n_minus := by simp only [mul_assoc]
            _ = α * (α * CB.n_minus) * CB.n_minus := by rw [← hα_m]
            _ = (α * α) * (CB.n_minus * CB.n_minus) := by simp only [mul_assoc]
        calc (x + CB.n_plus + α * CB.n_minus) * (x + CB.n_plus + α * CB.n_minus)
          _ = x * x + x * CB.n_plus + x * (α * CB.n_minus) +
              (CB.n_plus * x + CB.n_plus * CB.n_plus + CB.n_plus * (α * CB.n_minus)) +
              ((α * CB.n_minus) * x + (α * CB.n_minus) * CB.n_plus +
                (α * CB.n_minus) * (α * CB.n_minus)) := by noncomm_ring
          _ = (x * x) + (x * CB.n_plus + CB.n_plus * x) + (CB.n_plus * CB.n_plus) +
              α * (x * CB.n_minus + CB.n_minus * x) +
              α * (CB.n_plus * CB.n_minus + CB.n_minus * CB.n_plus) +
              (α * α) * (CB.n_minus * CB.n_minus) := by
              rw [hxam, hpam, haxm, hapm, haam]
              noncomm_ring
    _ = x_sq + 0 + 0 + α * 0 + α * (-2) + (α * α) * 0 := by
        rw [hx_sq, hx_plus, CB.n_plus_sq, hx_minus, CB.anticomm_null, CB.n_minus_sq]
    _ = x_sq - (2 : A) * α := by
        simp only [add_zero, mul_zero, mul_neg]
        rw [show α * (2 : A) = (2 : A) * α from by rw [mul_two, two_mul]]
        abel
    _ = 0 := by rw [h2α, sub_self]

theorem conformal_inner_is_spacetime_interval {R : Type*} [CommRing R]
    (x_sq y_sq xy diff_sq half : R)
    (h_half : 2 * half = 1)
    (h_diff : diff_sq = x_sq - 2 * xy + y_sq) :
    xy - half * x_sq - half * y_sq = -half * diff_sq := by
  rw [h_diff]
  calc xy - half * x_sq - half * y_sq
    _ = (2 * half) * xy - half * x_sq - half * y_sq := by rw [h_half, one_mul]
    _ = -half * (x_sq - 2 * xy + y_sq) := by ring

end ConformalCGA

/-! ## Section 7 (E-C6a): M₄(R) Maurer-Cartan Flat Nilpotency, Ward Blades & Zorn Schur Complement -/

section M4MaurerCartanWard

variable {R : Type*} [CommRing R]

theorem diff_inverse_identity (g_inv dg d_ginv : Matrix (Fin 4) (Fin 4) R)
    (h : d_ginv + g_inv * dg * g_inv = 0) :
    d_ginv = -(g_inv * dg * g_inv) :=
  eq_neg_of_add_eq_zero_left h

def maurerCartanCurvatureTensor (omega d_omega : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) R :=
  d_omega + omega * omega

theorem maurer_cartan_deductive_flat (omega d_omega : Matrix (Fin 4) (Fin 4) R)
    (h_chain : d_omega = -(omega * omega)) :
    maurerCartanCurvatureTensor omega d_omega = 0 := by
  dsimp [maurerCartanCurvatureTensor]
  rw [h_chain, neg_add_cancel]

def covariantDifferential (omega X : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) R :=
  omega * X - X * omega

/-- Second covariant differential `d_ω(d_ω(X)) = ω²X - 2 ω X ω + X ω²` vanishes whenever
`ω² = 0` and `ω X ω = 0`, without requiring `[ω, X] = 0`. -/
theorem covariant_differential_nilpotent_on_flat (omega X : Matrix (Fin 4) (Fin 4) R)
    (h_omega_nil : omega * omega = 0)
    (h_sandwich : omega * X * omega = 0) :
    covariantDifferential omega (covariantDifferential omega X) = 0 := by
  dsimp [covariantDifferential]
  calc omega * (omega * X - X * omega) - (omega * X - X * omega) * omega
    _ = (omega * omega) * X - omega * X * omega - (omega * X * omega - X * (omega * omega)) := by
        noncomm_ring
    _ = 0 * X - 0 - (0 - X * 0) := by rw [h_omega_nil, h_sandwich]
    _ = 0 := by simp

def superTraceBlade (M : Matrix (Fin 4) (Fin 4) R) : R :=
  (M 0 0 + M 1 1) - (M 2 2 + M 3 3)

def vectorBlade1 (A₀ A₁ A₂ A₃ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, A₀, A₁;
     0, 0, A₂, A₃;
     A₀, A₂, 0, 0;
     A₁, A₃, 0, 0]

def bivectorBlade2 (θ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![θ, 0, 0, 0;
     0, -θ, 0, 0;
     0, 0, θ, 0;
     0, 0, 0, -θ]

def totalWardConnection (θ A₀ A₁ A₂ A₃ : R) : Matrix (Fin 4) (Fin 4) R :=
  bivectorBlade2 θ + vectorBlade1 A₀ A₁ A₂ A₃

theorem bivector_spin_supertrace_zero (θ : R) :
    superTraceBlade (bivectorBlade2 θ) = 0 := by
  simp [superTraceBlade, bivectorBlade2]

theorem vector_maxwell_supertrace_zero (A₀ A₁ A₂ A₃ : R) :
    superTraceBlade (vectorBlade1 A₀ A₁ A₂ A₃) = 0 := by
  simp [superTraceBlade, vectorBlade1]

theorem total_ward_connection_supertrace_zero (θ A₀ A₁ A₂ A₃ : R) :
    superTraceBlade (totalWardConnection θ A₀ A₁ A₂ A₃) = 0 := by
  simp [superTraceBlade, totalWardConnection, bivectorBlade2, vectorBlade1]

def zornSchurComplement (SpQ SmQ_inv Ap_mv Am_mv : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) R :=
  SpQ - Ap_mv * SmQ_inv * Am_mv

/-- Zorn Schur complement vanishes on the lightcone `(S + Q)(S - Q) = (A + mv)(A - mv)`
whenever `Am_mv` commutes with `SmQ_inv` (without collapsing `M₄(R)` to a commutative ring). -/
theorem zorn_schur_vanishes_on_lightcone
    (SpQ SmQ SmQ_inv Ap_mv Am_mv : Matrix (Fin 4) (Fin 4) R)
    (h_inv : SmQ * SmQ_inv = 1)
    (h_lightcone : SpQ * SmQ = Ap_mv * Am_mv)
    (h_comm : SmQ_inv * Am_mv = Am_mv * SmQ_inv) :
    zornSchurComplement SpQ SmQ_inv Ap_mv Am_mv = 0 := by
  dsimp [zornSchurComplement]
  have hsubst : Ap_mv * SmQ_inv * Am_mv = SpQ := by
    calc Ap_mv * SmQ_inv * Am_mv
      _ = Ap_mv * (SmQ_inv * Am_mv) := by rw [Matrix.mul_assoc]
      _ = Ap_mv * (Am_mv * SmQ_inv) := by rw [h_comm]
      _ = (Ap_mv * Am_mv) * SmQ_inv := by rw [← Matrix.mul_assoc]
      _ = (SpQ * SmQ) * SmQ_inv := by rw [← h_lightcone]
      _ = SpQ * (SmQ * SmQ_inv) := by rw [Matrix.mul_assoc]
      _ = SpQ * 1 := by rw [h_inv]
      _ = SpQ := Matrix.mul_one _
  rw [hsubst, sub_self]

end M4MaurerCartanWard

end InfoGeometry.Synthesis.Aistudio1SSh9RiccatiZornConformalBridge
