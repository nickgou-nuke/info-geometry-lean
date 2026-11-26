/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
import InfoGeometry.Canonical.DoubledMinkowskiSpinFrameInstability
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import InfoGeometry.Canonical.MachianFrameDraggingBridge
import InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
import InfoGeometry.Canonical.RoadToGravityFromSpinning
import InfoGeometry.Canonical.RealDiracPalatiniVariationBridge
import Mathlib.Tactic

/-!
# Doubled Minkowski Spin-Frame Instability to Real Dirac–Cartan–Palatini Gravity Capstone

Bridges the complex and real rotating-spin-frame owners (`DoubledMinkowskiSpinFrameInstability`,
`DoubledMinkowskiRotatingSpinInstability`, `MachianFrameDraggingBridge`) directly into the
Einstein–Cartan torsion and MacDowell–Mansouri / Palatini variational corridor
(`GeometroMagnetoGravityCrankingDirac`, `RoadToGravityFromSpinning`,
`RealDiracPalatiniVariationBridge`):

1. **Real-to-Complex Spin-Frame Isomorphism (`real_to_complex_spin_frame_isomorphism`)**:
   Proves entry-by-entry under `Complex.ofReal` that the pure-real `Cl(1,1)` operators `swapOp4`,
   `singletProj4`, `tripletProj4`, `totalSpinZ4`, and `(1 / 4) • spinExchange4` embed onto
   `swapSpin`, `projSinglet`, `projTriplet`, `totSpinZ`, and `(1 / 2) • totSpinCasimir - (3 / 4) • 1`.
2. **Coriolis, Krein-Collision, & Machian ZAMO Restoration (`coriolis_krein_zamo_gap_restoration_bridge`)**:
   Unifies the complex BdG Coriolis threshold (`Ω_eff = m`, `m < Ω_eff`), the real exchange
   condensation gap `J - Ω_eff`, the signature-`(2,2)` Krein-collision trichotomy, and simultaneous
   Machian ZAMO restoration (`ω = Ω_drag`) of both the real singlet–triplet gap `J` and the
   complex BdG quasiparticle mass gap `m`.
3. **End-to-End Spin-to-Cartan–Palatini Capstone (`bdg_spin_to_cartan_palatini_end_to_end_capstone`)**:
   Composes `bdg_gapped_spectrum_and_particle_hole_symmetry`, `real_to_complex_spin_frame_isomorphism`,
   `coriolis_krein_zamo_gap_restoration_bridge`, the stationary Einstein–Cartan torsion lock
   `T = κ_EC J₅` with on-shell Fierz–Kofink–Rodichev invariant, and the real `M₄(ℝ)` Palatini
   `δe` variation + cosmological Einstein–de Sitter locus `2 R + Λ E₀ = 0`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `exists_noncomm_mat2x2_real_cap`, `exists_noncomm_mat2x2_complex_cap`
* `real_to_complex_spin_frame_isomorphism`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `coriolis_krein_zamo_gap_restoration_bridge` (`0 < m`)
* `bdg_spin_to_cartan_palatini_end_to_end_capstone` (`ξᵀ = ξ`, `0 < m`)

#### BUCKET 3: OPEN CLOSURE DEBT
* Continuum 4D curved-spacetime QFT existence/mass gap and dynamic coupled Einstein–Cartan–Dirac
  PDEs remain outside this finite-dimensional / colimit-algebraic capstone bridge.
-/

set_option autoImplicit false

noncomputable section

open scoped Kronecker
open Matrix
open InfoGeometry.OperatorAlgebra

namespace InfoGeometry.Canonical.DoubledMinkowskiSpinToGravityCapstone

/-- Explicit non-commutativity witness on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ`. -/
theorem exists_noncomm_mat2x2_real_cap :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, A * B ≠ B * A :=
  DoubledMinkowskiRotatingSpinInstability.exists_noncomm_mat2x2_real_spin

/-- Explicit non-commutativity witness on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`. -/
theorem exists_noncomm_mat2x2_complex_cap :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, A * B ≠ B * A :=
  DoubledMinkowskiSpinFrameInstability.exists_noncomm_mat2x2_complex

/-! ### Part 1: Real `Cl(1,1)` → Complex `M₄(ℂ)` Spin-Frame Isomorphism -/

private lemma scalar_real_to_complex_exchange_coeff (J Ω c : ℝ) :
    ((J / 4 : ℝ) * c : ℝ) = (J : ℂ) * ((1 / 4 : ℂ) * (c : ℂ)) := by
  push_cast
  ring

private lemma scalar_real_to_complex_ham_entry (J Ω ex sz : ℝ) :
    ((J / 4 * ex - Ω * sz : ℝ) : ℂ) =
      (J : ℂ) * ((1 / 4 : ℂ) * (ex : ℂ)) - (Ω : ℂ) * (sz : ℂ) := by
  push_cast
  ring

/-- **Theorem 1 (Exact Embedding of Real `Cl(1,1)` Spin Operators into `M₄(ℂ)`)**:
Under `Complex.ofReal` entrywise lift, `- ε ⊗ ε` matches `+ σ_y ⊗ σ_y`, identifying `swapOp4`,
`singletProj4`, `tripletProj4`, `totalSpinZ4`, `(1 / 4) • spinExchange4`, and
`rotatingSpinHamiltonian J Ω` with their complex counterparts in
`DoubledMinkowskiSpinFrameInstability`. -/
theorem real_to_complex_spin_frame_isomorphism (J Ω : ℝ) :
    (DoubledMinkowskiRotatingSpinInstability.swapOp4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.swapSpin) ∧
    (DoubledMinkowskiRotatingSpinInstability.singletProj4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.projSinglet) ∧
    (DoubledMinkowskiRotatingSpinInstability.tripletProj4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.projTriplet) ∧
    (DoubledMinkowskiRotatingSpinInstability.totalSpinZ4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.totSpinZ) ∧
    (((1 / 4 : ℝ) • DoubledMinkowskiRotatingSpinInstability.spinExchange4).map Complex.ofReal =
      (1 / 2 : ℂ) • DoubledMinkowskiSpinFrameInstability.totSpinCasimir -
        (3 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ∧
    ((DoubledMinkowskiRotatingSpinInstability.rotatingSpinHamiltonian J Ω).map Complex.ofReal =
      (J : ℂ) • ((1 / 2 : ℂ) • DoubledMinkowskiSpinFrameInstability.totSpinCasimir -
        (3 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) -
        (Ω : ℂ) • DoubledMinkowskiSpinFrameInstability.totSpinZ) := by
  have hCas : DoubledMinkowskiSpinFrameInstability.totSpinCasimir =
      (2 : ℂ) • DoubledMinkowskiSpinFrameInstability.projTriplet :=
    (DoubledMinkowskiSpinFrameInstability.singlet_triplet_decomposition_and_rotation 0).2.2.2.2.2.2.1
  have hSwap : DoubledMinkowskiRotatingSpinInstability.swapOp4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.swapSpin := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp [DoubledMinkowskiRotatingSpinInstability.swapOp4,
        DoubledMinkowskiRotatingSpinInstability.spinExchange4,
        DoubledMinkowskiBdGColimitBridge.zCut2,
        DoubledMinkowskiBdGColimitBridge.xMir2,
        DoubledMinkowskiRotatingSpinInstability.eps2,
        DoubledMinkowskiSpinFrameInstability.swapSpin,
        Matrix.kroneckerMap_apply] <;> norm_num
  have hSing : DoubledMinkowskiRotatingSpinInstability.singletProj4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.projSinglet := by
    unfold DoubledMinkowskiRotatingSpinInstability.singletProj4
      DoubledMinkowskiSpinFrameInstability.projSinglet
    ext p q
    have hpq := congrFun (congrFun hSwap p) q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] at hpq ⊢
    rw [hpq]
    split_ifs <;> simp
  have hTrip : DoubledMinkowskiRotatingSpinInstability.tripletProj4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.projTriplet := by
    unfold DoubledMinkowskiRotatingSpinInstability.tripletProj4
      DoubledMinkowskiSpinFrameInstability.projTriplet
    ext p q
    have hpq := congrFun (congrFun hSwap p) q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] at hpq ⊢
    rw [hpq]
    split_ifs <;> simp
  have hZ : DoubledMinkowskiRotatingSpinInstability.totalSpinZ4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.totSpinZ := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp [DoubledMinkowskiRotatingSpinInstability.totalSpinZ4,
        DoubledMinkowskiBdGColimitBridge.zCut2,
        DoubledMinkowskiSpinFrameInstability.totSpinZ,
        DoubledMinkowskiSpinFrameInstability.pauliZ,
        Matrix.kroneckerMap_apply] <;> norm_num
  have hEx : ((1 / 4 : ℝ) • DoubledMinkowskiRotatingSpinInstability.spinExchange4).map Complex.ofReal =
      (1 / 2 : ℂ) • DoubledMinkowskiSpinFrameInstability.totSpinCasimir -
        (3 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    rw [hCas]
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp [DoubledMinkowskiRotatingSpinInstability.spinExchange4,
        DoubledMinkowskiBdGColimitBridge.zCut2,
        DoubledMinkowskiBdGColimitBridge.xMir2,
        DoubledMinkowskiRotatingSpinInstability.eps2,
        DoubledMinkowskiSpinFrameInstability.projTriplet,
        DoubledMinkowskiSpinFrameInstability.swapSpin,
        Matrix.kroneckerMap_apply] <;> norm_num
  have hHam : (DoubledMinkowskiRotatingSpinInstability.rotatingSpinHamiltonian J Ω).map Complex.ofReal =
      (J : ℂ) • ((1 / 2 : ℂ) • DoubledMinkowskiSpinFrameInstability.totSpinCasimir -
        (3 / 4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) -
        (Ω : ℂ) • DoubledMinkowskiSpinFrameInstability.totSpinZ := by
    rw [← hEx, ← hZ]
    unfold DoubledMinkowskiRotatingSpinInstability.rotatingSpinHamiltonian
    ext p q
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_one]
    ring
  exact ⟨hSwap, hSing, hTrip, hZ, hEx, hHam⟩

/-! ### Part 2: Coriolis Collapse, Krein-Collision, & Machian ZAMO Restoration -/

private lemma scalar_sqrt_sq_of_pos {m : ℝ} (hm : 0 < m) :
    Real.sqrt (0 ^ 2 + m ^ 2) - 0 = m := by
  rw [zero_pow (by norm_num), zero_add, sub_zero, Real.sqrt_sq hm.le]

/-- **Theorem 2 (Coriolis–Krein Instability & Machian ZAMO Gap Restoration Bridge)**:
For any positive pairing gap `m > 0`, exchange coupling `J`, Krein sheet mixing `g`, observer
frame rate `ω`, and frame-dragging rate `Ω_drag` (`Ω_eff := ω - Ω_drag`):
1. Singlet BdG immunity + triplet Coriolis collapse (`Ω_eff = m`, `m < Ω_eff`).
2. Real singlet → triplet exchange gap `E_{T,+1} - E_S = J - Ω_eff`.
3. Krein-collision Jordan threshold (`|Ω_eff| = |g|`) and exponential runaway (`|Ω_eff| < |g|`).
4. **Machian ZAMO Restoration (`ω = Ω_drag`)**: Zeeman splitting vanishes (`E_{T,-1} = E_{T,+1}`),
   the rest-frame singlet–triplet gap `J` is restored, the complex BdG triplet quasiparticle restores
   its mass gap `m`, and `frameDraggedSpinHamiltonian J ω Ω_drag` equals `(J / 4) • spinExchange4`. -/
theorem coriolis_krein_zamo_gap_restoration_bridge
    {m : ℝ} (hm : 0 < m) (J ω Ω_drag g t : ℝ) (a b : ℂ) :
    let Ω_eff := ω - Ω_drag
    (m ^ 2 * (2 * (Complex.normSq a + Complex.normSq b)) ≤
      ∑ p, Complex.normSq
        ((DoubledMinkowskiSpinFrameInstability.bdgSpinRotHam 0 m Ω_eff).mulVec
          (DoubledMinkowskiSpinFrameInstability.doubledSinglet a b) p)) ∧
    ((DoubledMinkowskiSpinFrameInstability.bdgSpinRotHam 0 m m).mulVec
      (DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m) = 0) ∧
    (m < Ω_eff →
      (DoubledMinkowskiSpinFrameInstability.bdgSpinRotHam 0 m Ω_eff).mulVec
        (DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m) =
        (((m - Ω_eff : ℝ) : ℂ)) •
          DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m ∧
      m - Ω_eff < 0) ∧
    (((1 / 4 : ℝ) * J - Ω_eff) - -(3 / 4 : ℝ) * J = J - Ω_eff) ∧
    (Ω_eff ≠ 0 →
      g = Ω_eff →
      DoubledMinkowskiSpinFrameInstability.kreinCollisionOp Ω_eff g ≠ 0 ∧
      DoubledMinkowskiSpinFrameInstability.kreinCollisionOp Ω_eff g *
        DoubledMinkowskiSpinFrameInstability.kreinCollisionOp Ω_eff g = 0) ∧
    (|Ω_eff| < |g| →
      let γ := Real.sqrt (g ^ 2 - Ω_eff ^ 2)
      let U_hyp := Real.cosh (γ * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
        (Real.sinh (γ * t) / γ) • DoubledMinkowskiSpinFrameInstability.kreinCollisionOp Ω_eff g
      let v_run := (DoubledMinkowskiSpinFrameInstability.kreinCollisionOp Ω_eff g + γ • 1).mulVec
        (fun p => if p = (0, 0) then 1 else 0)
      0 < γ ∧ U_hyp.mulVec v_run = Real.exp (γ * t) • v_run) ∧
    (ω = Ω_drag →
      ((1 / 4 : ℝ) * J + (ω - Ω_drag) = (1 / 4 : ℝ) * J - (ω - Ω_drag)) ∧
      ((1 / 4 : ℝ) * J - (ω - Ω_drag)) - -(3 / 4 : ℝ) * J = J ∧
      (DoubledMinkowskiSpinFrameInstability.bdgSpinRotHam 0 m Ω_eff).mulVec
        (DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m) =
        (m : ℂ) • DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m ∧
      MachianFrameDraggingBridge.frameDraggedSpinHamiltonian J ω Ω_drag =
        (J / 4 : ℝ) • DoubledMinkowskiRotatingSpinInstability.spinExchange4) := by
  dsimp
  have hBdg := DoubledMinkowskiSpinFrameInstability.rotating_bdg_singlet_stability_vs_triplet_instability
    0 m (ω - Ω_drag) a b
  have hCor := DoubledMinkowskiSpinFrameInstability.triplet_coriolis_gap_closure_and_instability
    (Ω := ω - Ω_drag) hm
  have hReal := DoubledMinkowskiRotatingSpinInstability.real_rotating_frame_singlet_triplet_instability
    J (ω - Ω_drag)
  have hKrein := DoubledMinkowskiSpinFrameInstability.krein_collision_phase_transition
    (ω - Ω_drag) g t
  have hZamo := MachianFrameDraggingBridge.zamo_triplet_zeeman_splitting_cancellation J ω Ω_drag
  refine ⟨hBdg.2.2.1, hCor.2.1, hCor.2.2, hReal.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro hNe hg
    subst hg
    exact ⟨(hKrein.2.2.1 hNe).1, (hKrein.2.2.1 hNe).2.1⟩
  · intro hlt
    exact ⟨(hKrein.2.2.2.1 hlt).1, (hKrein.2.2.2.1 hlt).2.2.2.2⟩
  · intro hEq
    have hZeq : (1 / 4 : ℝ) * J + (ω - Ω_drag) = (1 / 4 : ℝ) * J - (ω - Ω_drag) :=
      hZamo.2.2.2.1.mpr hEq
    have hGap := (hZamo.2.2.2.2 hEq).1
    have hBdg0 :=
      (DoubledMinkowskiSpinFrameInstability.rotating_bdg_singlet_stability_vs_triplet_instability
        0 m 0 a b).2.2.2.1
    rw [scalar_sqrt_sq_of_pos hm] at hBdg0
    have hEff0 : ω - Ω_drag = 0 := sub_eq_zero.mpr hEq
    refine ⟨hZeq, hGap, ?_, ?_⟩
    · rw [hEff0]
      exact hBdg0
    · unfold MachianFrameDraggingBridge.frameDraggedSpinHamiltonian
        DoubledMinkowskiRotatingSpinInstability.rotatingSpinHamiltonian
      rw [hEff0, zero_smul, sub_zero]

/-! ### Part 3: End-to-End BdG Spin-Frame to Cartan–Palatini Gravity Capstone -/

/-- **Theorem 3 (End-to-End Spin-to-Gravity Synthesis)**:
Connects across all seven canonical owners:
1. Gapped `2n × 2n` BdG spectrum & particle–hole symmetry (`DoubledMinkowskiBdGColimitBridge`).
2. Real-to-complex spin-exchange equivalence (`real_to_complex_spin_frame_isomorphism`).
3. ZAMO frame-dragging Zeeman cancellation & BdG rest-frame gap restoration (`ω = Ω_drag`).
4. Stationary Einstein–Cartan axial torsion–spin lock `T = κ_EC J₅` with on-shell
   Fierz–Kofink–Rodichev invariant `(1/2) κ_EC² (Ω₁² + Ω₂²)`.
5. Real `M₄(ℝ)` MacDowell–Mansouri `δe` variation, Hodge-dual Palatini contraction
   `Tr(γ₅ Σ₀₁ [e₂, e₃]) = -1`, and de Sitter stationarity `2 R + Λ E₀ = 0`. -/
theorem bdg_spin_to_cartan_palatini_end_to_end_capstone
    {n : ℕ} (ξ : Matrix (Fin n) (Fin n) ℝ) (hξ : ξᵀ = ξ)
    {m : ℝ} (hm : 0 < m) (ψ : Fin n ⊕ Fin n → ℝ)
    (J ω Ω_drag κ_EC Λ : ℝ)
    (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ)
    (T δT : Fin 4 → ℝ)
    (R E₀ e₁ δe e₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    let H_bdg := DoubledMinkowskiBdGColimitBridge.bdgHamiltonian ξ m
    let j5 := GeometroMagnetoGravityCrankingDirac.diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω₁ := GeometroMagnetoGravityCrankingDirac.diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω₂ := GeometroMagnetoGravityCrankingDirac.diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    (m ^ 2 * dotProduct ψ ψ ≤ dotProduct ψ ((H_bdg * H_bdg).mulVec ψ) ∧
      (H_bdg.mulVec ψ = 0 → ψ = 0)) ∧
    (DoubledMinkowskiRotatingSpinInstability.swapOp4.map Complex.ofReal =
      DoubledMinkowskiSpinFrameInstability.swapSpin) ∧
    (ω = Ω_drag →
      (DoubledMinkowskiSpinFrameInstability.bdgSpinRotHam 0 m (ω - Ω_drag)).mulVec
        (DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m) =
        (m : ℂ) • DoubledMinkowskiSpinFrameInstability.tripletQuasiPlus 0 m ∧
      ((1 / 4 : ℝ) * J - (ω - Ω_drag)) - -(3 / 4 : ℝ) * J = J) ∧
    (HasDerivAt
        (fun ε : ℝ => RealDiracPalatiniVariationBridge.ecTorsionSpinLagrangian κ_EC
          (fun μ => T μ + ε * δT μ) j5)
        (GeometroMagnetoGravityCrankingDirac.minkPair δT (fun μ => T μ - κ_EC * j5 μ)) 0 ∧
      RealDiracPalatiniVariationBridge.ecTorsionSpinLagrangian κ_EC (fun μ => κ_EC * j5 μ) j5 =
        (1 / 2 : ℝ) * κ_EC ^ 2 * (Ω₁ ^ 2 + Ω₂ ^ 2)) ∧
    (HasDerivAt (fun ε : ℝ => RealDiracPalatiniVariationBridge.mmPalatiniAction R E₀ Λ (e₁ + ε • δe) e₂)
        (Matrix.trace (δe * PeirceSpine.comm e₂
          (DiracSpinCasimirNambuModulesBridge.diracOmega4 * ((2 : ℝ) • R + Λ • E₀)))) 0 ∧
      ((2 : ℝ) • R + Λ • E₀ = 0 →
        Matrix.trace (δe * PeirceSpine.comm e₂
          (DiracSpinCasimirNambuModulesBridge.diracOmega4 * ((2 : ℝ) • R + Λ • E₀))) = 0) ∧
      Matrix.trace (DiracSpinCasimirNambuModulesBridge.diracOmega4 *
        RoadToGravityFromSpinning.spinBiv 0 1 *
        PeirceSpine.comm (RoadToGravityFromSpinning.solderVec 2)
          (RoadToGravityFromSpinning.solderVec 3)) = -1) := by
  dsimp
  have hStage1 := DoubledMinkowskiBdGColimitBridge.bdg_gapped_spectrum_and_particle_hole_symmetry
    ξ hξ m ψ
  have hStage2 := real_to_complex_spin_frame_isomorphism J ω
  have hStage3 := coriolis_krein_zamo_gap_restoration_bridge hm J ω Ω_drag 1 0 0 0
  have hStage4 := RealDiracPalatiniVariationBridge.einstein_cartan_delta_omega_and_torsion_spin_lock
    0 0 0 0 0 κ_EC T δT (GeometroMagnetoGravityCrankingDirac.diracAxialCurrent
      a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂)
  have hStage5 := RealDiracPalatiniVariationBridge.palatini_delta_e_variation_and_lambda_eq
    R E₀ e₁ δe e₂ Λ
  have hPal := (RoadToGravityFromSpinning.soldering_commutators_generate_spin_and_palatini_gravity
    0 0 0).2.2.2.1
  refine ⟨⟨hStage1.2.2.2.2.1, hStage1.2.2.2.2.2 hm.ne'⟩, hStage2.1, ?_, ?_, ?_⟩
  · intro hEq
    exact ⟨(hStage3.2.2.2.2.2.2 hEq).2.2.1, (hStage3.2.2.2.2.2.2 hEq).2.1⟩
  · exact ⟨hStage4.2.2.1, hStage4.2.2.2.2.2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂⟩
  · exact ⟨hStage5.1, fun hVac => hStage5.2.1 hVac δe, hPal⟩

end InfoGeometry.Canonical.DoubledMinkowskiSpinToGravityCapstone
