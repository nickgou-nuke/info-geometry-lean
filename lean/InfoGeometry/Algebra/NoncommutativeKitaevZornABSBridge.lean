/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
import InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
import InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis
import InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
import InfoGeometry.Quantum.KitaevPauliBraiding
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevLocalGapOmegaSpectrumPoset
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset
import Mathlib.Tactic

/-!
# Intertwining Bridge: Noncommutative Kitaev–Zorn–Majorana ↔ ABS Clifford & Local-Gap Owners

Connects the noncommutative `M₂(B)` / `M₂(M₂(B))` Kitaev–Majorana–Kramers family
with the preexisting `KitaevABSCliffordExtensionMassDichotomyPoset` and
`KitaevLocalGapOmegaSpectrumPoset` owners:

1. **Generator & Klein-Twist Identification (`Mat2` ↔ `NoncommutativeCliffordPrimitives`)**:
   `gamma1Op = Mat2.sigmaZ`, `sigmaOp = Mat2.sigmaX`, `omegaOp = -Mat2.massJ`, and
   `sympTimeRev X = Mat2.kleinAdjointB (Xᴴ)`.
2. **4×4 Flattening Ring Homomorphism (`NestedMat B →+* Matrix (Fin 4) (Fin 4) B`)**:
   `nestedToMat4` transports `kitaevGaugeD^2 = 1`, `kitaevSpin1 * kitaevSpin2 * kitaevSpin3 = -kitaevGaugeD`,
   and zero-field sublattice anticommutation into `Matrix (Fin 4) (Fin 4) B`.
3. **Dirac-Cone Haldane Gap ↔ Local-Gap Collar Decoupling (`N_plus`, `N_minus`)**:
   At the Dirac cone (`K₁² + K₂² - K₃² = 0`, commuting couplings), `H_Δ^2` decouples
   across `cantorProj 1`: `N_plus (cantorProj 1) (H_Δ * H_Δ) = 0` and
   `N_minus (cantorProj 1) (H_Δ * H_Δ) = 0`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
open InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
open InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis

namespace InfoGeometry.Algebra.NoncommutativeKitaevZornABSBridge

/-! ## Bridge 1: `Mat2` Clifford Generators & `kleinAdjointB` ↔ `sympTimeRev` -/

section Mat2CliffordBridge

theorem clifford_generators_eq_abs_mat2 {K : Type*} [CommRing K] :
    (gamma1Op : Matrix (Fin 2) (Fin 2) K) =
      InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.sigmaZ ∧
    (sigmaOp : Matrix (Fin 2) (Fin 2) K) =
      InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.sigmaX ∧
    (omegaOp : Matrix (Fin 2) (Fin 2) K) =
      -InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.massJ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> simp [gamma1Op, sigmaOp, omegaOp,
      InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.sigmaZ,
      InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.sigmaX,
      InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.massJ])

theorem sympTimeRev_eq_kleinAdjointB_conjTranspose {K : Type*} [CommRing K] [StarRing K]
    (X : Matrix (Fin 2) (Fin 2) K) :
    sympTimeRev X =
      InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.kleinAdjointB (Xᴴ) := by
  have hω : (omegaOp : Matrix (Fin 2) (Fin 2) K) =
      -InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.massJ :=
    (clifford_generators_eq_abs_mat2 (K := K)).2.2
  dsimp [sympTimeRev,
    InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset.Mat2.kleinAdjointB]
  rw [hω]
  noncomm_ring

end Mat2CliffordBridge

/-! ## Bridge 2: `NestedMat B →+* Matrix (Fin 4) (Fin 4) B` Flattening Homomorphism -/

section NestedToMat4Bridge

/-- Flattening ring homomorphism `M₂(M₂(B)) →+* M₄(B)` via `finProdFinEquiv (m := 2) (n := 2)`. -/
def nestedToMat4 {B : Type*} [Ring B] : NestedMat B →+* Matrix (Fin 4) (Fin 4) B where
  toFun M i j :=
    let p := (finProdFinEquiv (m := 2) (n := 2)).symm i
    let q := (finProdFinEquiv (m := 2) (n := 2)).symm j
    M p.1 q.1 p.2 q.2
  map_zero' := rfl
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]
  map_add' A C := by
    ext i j
    rfl
  map_mul' A C := by
    set_option maxHeartbeats 1000000 in
    ext i j
    dsimp only
    rw [Matrix.mul_apply]
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    symm
    erw [Matrix.mul_apply]
    rw [← (finProdFinEquiv (m := 2) (n := 2)).sum_comp]
    simp only [Fintype.sum_prod_type, Equiv.symm_apply_apply]

@[simp] theorem nestedToMat4_apply {B : Type*} [Ring B] (M : NestedMat B) (i j : Fin 4) :
    nestedToMat4 M i j =
      M ((finProdFinEquiv (m := 2) (n := 2)).symm i).1
        ((finProdFinEquiv (m := 2) (n := 2)).symm j).1
        ((finProdFinEquiv (m := 2) (n := 2)).symm i).2
        ((finProdFinEquiv (m := 2) (n := 2)).symm j).2 := rfl

theorem nestedToMat4_kitaev_fractionalization {B : Type*} [Ring B] :
    nestedToMat4 (kitaevGaugeD : NestedMat B) * nestedToMat4 kitaevGaugeD = 1 ∧
    nestedToMat4 (kitaevSpin1 : NestedMat B) *
      nestedToMat4 (kitaevSpin2 : NestedMat B) *
      nestedToMat4 (kitaevSpin3 : NestedMat B) =
      -nestedToMat4 (kitaevGaugeD : NestedMat B) := by
  have h := kitaev_majorana_fractionalization_and_three_spin_identity (B := B)
  refine ⟨?_, ?_⟩
  · rw [← map_mul, h.1, map_one]
  · rw [← map_mul, ← map_mul, h.2.2.2.2.2.2.2, map_neg]

/-- The split-sign four-generator model becomes the repository's self-adjoint
four-Majorana Pauli model after complexifying its two square-`-1` generators.
This identifies the actual `4 × 4` matrices, not merely their abstract
Clifford relations. -/
theorem nestedToMat4_split_generators_eq_pauliMajorana :
    nestedToMat4 (majC : NestedMat ℂ) =
        InfoGeometry.Quantum.KitaevChain.pauliMajorana0 ∧
    (Complex.I : ℂ) • nestedToMat4 (majB1 : NestedMat ℂ) =
        InfoGeometry.Quantum.KitaevChain.pauliMajorana1 ∧
    nestedToMat4 (majB2 : NestedMat ℂ) =
        InfoGeometry.Quantum.KitaevChain.pauliMajorana2 ∧
    (Complex.I : ℂ) • nestedToMat4 (majB3 : NestedMat ℂ) =
        InfoGeometry.Quantum.KitaevChain.pauliMajorana3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nestedToMat4_apply, majC, mat2,
        InfoGeometry.Quantum.KitaevChain.pauliMajorana0,
        finProdFinEquiv, Fin.divNat, Fin.modNat]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nestedToMat4_apply, majB1, mat2,
        InfoGeometry.Quantum.KitaevChain.pauliMajorana1,
        finProdFinEquiv, Fin.divNat, Fin.modNat, Complex.I_mul_I]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nestedToMat4_apply, majB2, mat2, sigmaOp,
        InfoGeometry.Quantum.KitaevChain.pauliMajorana2,
        finProdFinEquiv, Fin.divNat, Fin.modNat]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nestedToMat4_apply, majB3, mat2, omegaOp,
        InfoGeometry.Quantum.KitaevChain.pauliMajorana3,
        finProdFinEquiv, Fin.divNat, Fin.modNat, Complex.I_mul_I]

theorem nestedToMat4_honeycomb_chiral_anticomm {B : Type*} [Ring B] (K₁ K₂ K₃ : B) :
    nestedToMat4 (kitaevHoneycombH 0 K₁ K₂ K₃) * nestedToMat4 sublatticeGamma +
      nestedToMat4 sublatticeGamma * nestedToMat4 (kitaevHoneycombH 0 K₁ K₂ K₃) = 0 := by
  have h0 : kitaevHoneycombH (0 : B) K₁ K₂ K₃ * sublatticeGamma +
      sublatticeGamma * kitaevHoneycombH (0 : B) K₁ K₂ K₃ = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [kitaevHoneycombH, InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis.bareDiracZorn,
        InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis.diracZornOp,
        sublatticeGamma, fiberEmbed]
  rw [← map_mul, ← map_mul, ← map_add, h0, map_zero]

end NestedToMat4Bridge

/-! ## Bridge 3: Dirac-Cone Haldane Gap ↔ Local-Gap Collar Decoupling (`N_plus`, `N_minus`) -/

section LocalGapCollarBridge

theorem kitaev_dirac_cone_collar_decoupling {B : Type*} [Ring B]
    (Δ_H K₁ K₂ K₃ : B)
    (h23 : ⁅K₂, K₃⁆ = 0) (h31 : ⁅K₃, K₁⁆ = 0) (h12 : ⁅K₁, K₂⁆ = 0)
    (hΔ1 : ⁅Δ_H, K₁⁆ = 0) (hΔ2 : ⁅Δ_H, K₂⁆ = 0) (hΔ3 : ⁅Δ_H, K₃⁆ = 0)
    (h_cone : K₁ * K₁ + K₂ * K₂ - K₃ * K₃ = 0) :
    let P : NestedMat B := cantorProj 1
    let H_Δ := kitaevHoneycombH Δ_H K₁ K₂ K₃
    KitaevLocalGapOmegaSpectrumPoset.N_plus P (H_Δ * H_Δ) = 0 ∧
    KitaevLocalGapOmegaSpectrumPoset.N_minus P (H_Δ * H_Δ) = 0 := by
  intro P H_Δ
  have hsq := (kitaev_dirac_cone_mass_square_and_sublattice_trace_sign_flip Δ_H K₁ K₂ K₃
    h23 h31 h12 hΔ1 hΔ2 hΔ3 h_cone).2.2.2.1
  rw [hsq]
  refine ⟨?_, ?_⟩
  · dsimp [KitaevLocalGapOmegaSpectrumPoset.N_plus, P, cantorProj]
    apply ext_fin2 <;> simp
  · dsimp [KitaevLocalGapOmegaSpectrumPoset.N_minus, P, cantorProj]
    apply ext_fin2 <;> simp

end LocalGapCollarBridge

/-! ## Bridge 4: `nestedToMat4` ↔ `ConcreteKitaevBdGMatrix` (`particleHole4`, `kitaevBdG4`) -/

section ConcreteBdGBridge

/-- Flattening the itinerant Majorana `majC : NestedMat ℂ` yields `ConcreteKitaevBdGMatrix.particleHole4`. -/
theorem nestedToMat4_majC_eq_particleHole4 :
    nestedToMat4 (majC : NestedMat ℂ) =
      InfoGeometry.Canonical.ConcreteKitaevBdGMatrix.particleHole4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majC, mat2, finProdFinEquiv, Fin.divNat, Fin.modNat,
      InfoGeometry.Canonical.ConcreteKitaevBdGMatrix.particleHole4]

/-- Flattening the nested `2×2` block Dirac–Bogoliubov operator recovers `ConcreteKitaevBdGMatrix.kitaevBdG4`. -/
theorem nestedToMat4_kitaevBdG4_eq (mu t delta : ℝ) :
    nestedToMat4 (mat2
      (-(mu : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (t : ℂ) • (sigmaOp : Matrix (Fin 2) (Fin 2) ℂ))
      (-(delta : ℂ) • (omegaOp : Matrix (Fin 2) (Fin 2) ℂ))
      ((delta : ℂ) • (omegaOp : Matrix (Fin 2) (Fin 2) ℂ))
      ((mu : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • (sigmaOp : Matrix (Fin 2) (Fin 2) ℂ))) =
      InfoGeometry.Canonical.ConcreteKitaevBdGMatrix.kitaevBdG4 mu t delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat2, sigmaOp, omegaOp, finProdFinEquiv, Fin.divNat, Fin.modNat,
      InfoGeometry.Canonical.ConcreteKitaevBdGMatrix.kitaevBdG4]

end ConcreteBdGBridge

/-- Explicit non-commutativity witness for `Matrix (Fin 4) (Fin 4) B` over any nontrivial ring. -/
theorem mat4_basis_noncommuting {B : Type*} [Ring B] [Nontrivial B] :
    ∃ A C : Matrix (Fin 4) (Fin 4) B, A * C ≠ C * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 0 then 1 else 0),
    Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0), ?_⟩
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  simp [Matrix.mul_apply] at h01

end InfoGeometry.Algebra.NoncommutativeKitaevZornABSBridge
