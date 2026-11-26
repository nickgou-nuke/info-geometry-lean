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
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
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
* `peirce_graded_cartan_maurer_cartan_unification`, `cartan_soldering_self_dual_yang_mills_exterior_bridge`,
  `cartan_curvature_torsion_split_colimit_lift`, `axial_spin_torsion_zamo_frame_dragging_singlet_triplet_capstone`

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

private lemma scalar_real_to_complex_exchange_coeff (J _Ω c : ℝ) :
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

/-! ### Part 4: Graded Cartan Connection → Peirce Maurer–Cartan, Self-Dual Yang–Mills, & `Limit` -/

section PeirceColimitBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.RoadToGravityFromSpinning
open InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
open InfoGeometry.Canonical.MachianFrameDraggingBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Physics.CrankingParity

/-- `evenGrade P X` commutes with `invS P` for any idempotent `P` in any associative ring `B`. -/
lemma invS_comm_evenGrade {B : Type*} [Ring B] {P : B} (hP : P * P = P) (X : B) :
    invS P * evenGrade P X = evenGrade P X * invS P := by
  simp only [invS, evenGrade]
  peirce_nf hP

/-- `oddGrade P X` anticommutes with `invS P` for any idempotent `P` in any associative ring `B`. -/
lemma invS_anticomm_oddGrade {B : Type*} [Ring B] {P : B} (hP : P * P = P) (X : B) :
    invS P * oddGrade P X = -(oddGrade P X * invS P) := by
  simp only [invS, oddGrade]
  peirce_nf hP

/-- `genPhi P A C` anticommutes with `invS P` for any idempotent `P` in any associative ring `B`. -/
lemma invS_anticomm_genPhi {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C = -(genPhi P A C * invS P) := by
  simp only [invS, genPhi, conePlus, coneMinus]
  peirce_nf hP

/-- **Theorem 4A (Graded Cartan Curvature/Torsion Split ↔ Peirce Maurer–Cartan & Self-Dual Yang–Mills)**:
Unifies `RoadToGravityFromSpinning.cartan_curvature_torsion_graded_split` with
`PeirceDefectBridge.peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills`. -/
theorem peirce_graded_cartan_maurer_cartan_unification {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (A₁ C₁ A₂ C₂ X₁ X₂ dX Y : B) :
    let Γ := invS P
    let ω₁ := evenGrade P X₁
    let ω₂ := evenGrade P X₂
    let dω := evenGrade P dX
    let e₁ := genPhi P A₁ C₁
    let e₂ := genPhi P A₂ C₂
    let de := oddGrade P dX
    let F₁₂ := (dω + de) + PeirceSpine.comm (ω₁ + e₁) (ω₂ + e₂)
    let R₁₂ := dω + PeirceSpine.comm ω₁ ω₂
    let E₁₂ := PeirceSpine.comm e₁ e₂
    let T₁₂ := de + PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁
    (F₁₂ = (R₁₂ + E₁₂) + T₁₂) ∧
    (Γ * (R₁₂ + E₁₂) = (R₁₂ + E₁₂) * Γ) ∧
    (Γ * T₁₂ = -(T₁₂ * Γ)) ∧
    ((R₁₂ + E₁₂) * (R₁₂ + E₁₂) = R₁₂ * R₁₂ + (R₁₂ * E₁₂ + E₁₂ * R₁₂) + E₁₂ * E₁₂) ∧
    (peirceGradingDeriv P (evenGrade P Y) = 0) ∧
    (peirceMaurerCartanCurvature P A₁ C₁ = genJ P A₁ C₁ + genV P A₁ C₁) ∧
    (parityConj P (genV P A₁ C₁) = genV P A₁ C₁) ∧
    (parityConj P (genJ P A₁ C₁) = -genJ P A₁ C₁) ∧
    (peirceCovariantDeriv P A₁ C₁ (genV P A₁ C₁) = 0) ∧
    (peirceCovariantDeriv P A₁ C₁ (parityConj P (genV P A₁ C₁)) = 0) := by
  have hSplit := cartan_curvature_torsion_graded_split (invS P)
    (evenGrade P X₁) (evenGrade P X₂) (evenGrade P dX)
    (genPhi P A₁ C₁) (genPhi P A₂ C₂) (oddGrade P dX)
    (invS_comm_evenGrade hP X₁) (invS_comm_evenGrade hP X₂) (invS_comm_evenGrade hP dX)
    (invS_anticomm_genPhi hP A₁ C₁) (invS_anticomm_genPhi hP A₂ C₂) (invS_anticomm_oddGrade hP dX)
  have hMC := peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP A₁ C₁ Y X₂
  exact ⟨hSplit.1, hSplit.2.1, hSplit.2.2.1, hSplit.2.2.2,
    hMC.2.1, hMC.2.2.1, hMC.2.2.2.2.2.1, hMC.2.2.2.2.2.2.1, hMC.2.2.2.2.2.2.2.2.2.1,
    hMC.2.2.2.2.2.2.2.2.2.2⟩

/-- **Theorem 4B (ExteriorAlgebra Carrier Bridge: Graded Cartan Soldering → Self-Dual Yang–Mills)**. -/
theorem cartan_soldering_self_dual_yang_mills_exterior_bridge
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V] {n : ℕ}
    (star d : Module.End R (ExteriorAlgebra R V))
    {P : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)} (hP : P * P = P)
    (A_op C_op X : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)) :
    let A_conn := genPhi P A_op C_op
    (invS P * evenGrade P X = evenGrade P X * invS P) ∧
    (invS P * A_conn = -(A_conn * invS P)) ∧
    (evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X) ∧
    (matrixExteriorDerivative d A_conn = peirceGradingDeriv P A_conn →
      curvatureFromConnection d A_conn = genJ P A_op C_op + genV P A_op C_op ∧
      evenGrade P (curvatureFromConnection d A_conn) = genV P A_op C_op) ∧
    (curvatureFromConnection 0 A_conn = genV P A_op C_op) ∧
    (covariantDerivative A_conn 0 (genV P A_op C_op) = 0) ∧
    (isSelfDualCurvature star (genV P A_op C_op) →
      covariantDerivative A_conn 0 (matrixHodgeStar star (curvatureFromConnection 0 A_conn)) = 0) := by
  have hYM := peirce_defect_connection_curvature_and_yang_mills_bridge star d hP A_op C_op X
  exact ⟨invS_comm_evenGrade hP X, invS_anticomm_genPhi hP A_op C_op,
    hYM.1, hYM.2.1, hYM.2.2.1, hYM.2.2.2.1, hYM.2.2.2.2⟩

/-- **Theorem 4C (Inductive-Colimit `Cl(1,1)^{⊗ n}` Lift of Graded Cartan Curvature/Torsion & Krein Polarization)**. -/
theorem cartan_curvature_torsion_split_colimit_lift
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (a : Stage k), tau (ofStage k a) = normalizedTrace k a)
    {n m : ℕ} (hnm : n ≤ m)
    {P₀ : Stage n} (hP₀ : P₀ * P₀ = P₀) (hP₀s : star P₀ = P₀)
    (A₀ C₀ A₂ C₂ X₁ X₂ dX : Stage n) :
    let bMap := bondMap stageBond n m hnm
    let P_L := ofStage n P₀
    let ω₁₀ := evenGrade P₀ X₁
    let ω₂₀ := evenGrade P₀ X₂
    let dω₀ := evenGrade P₀ dX
    let e₁₀ := genPhi P₀ A₀ C₀
    let e₂₀ := genPhi P₀ A₂ C₂
    let de₀ := oddGrade P₀ dX
    let F₁₂₀ := (dω₀ + de₀) + PeirceSpine.comm (ω₁₀ + e₁₀) (ω₂₀ + e₂₀)
    let R₁₂₀ := dω₀ + PeirceSpine.comm ω₁₀ ω₂₀
    let E₁₂₀ := PeirceSpine.comm e₁₀ e₂₀
    let T₁₂₀ := de₀ + PeirceSpine.comm ω₁₀ e₂₀ - PeirceSpine.comm ω₂₀ e₁₀
    let ω₁L := evenGrade P_L (ofStage n X₁)
    let ω₂L := evenGrade P_L (ofStage n X₂)
    let dωL := evenGrade P_L (ofStage n dX)
    let e₁L := genPhi P_L (ofStage n A₀) (ofStage n C₀)
    let e₂L := genPhi P_L (ofStage n A₂) (ofStage n C₂)
    let deL := oddGrade P_L (ofStage n dX)
    let F₁₂L := (dωL + deL) + PeirceSpine.comm (ω₁L + e₁L) (ω₂L + e₂L)
    let R₁₂L := dωL + PeirceSpine.comm ω₁L ω₂L
    let E₁₂L := PeirceSpine.comm e₁L e₂L
    let T₁₂L := deL + PeirceSpine.comm ω₁L e₂L - PeirceSpine.comm ω₂L e₁L
    (bMap F₁₂₀ = (bMap R₁₂₀ + bMap E₁₂₀) + bMap T₁₂₀) ∧
    (ofStage n R₁₂₀ = R₁₂L) ∧
    (ofStage n E₁₂₀ = E₁₂L) ∧
    (ofStage n T₁₂₀ = T₁₂L) ∧
    (ofStage n F₁₂₀ = F₁₂L) ∧
    (F₁₂L = (R₁₂L + E₁₂L) + T₁₂L) ∧
    (invS P_L * (R₁₂L + E₁₂L) = (R₁₂L + E₁₂L) * invS P_L) ∧
    (invS P_L * T₁₂L = -(T₁₂L * invS P_L)) ∧
    (0 ≤ limitKreinPairing tau P_L (P_L * ofStage n X₁) (P_L * ofStage n X₁)) ∧
    (limitKreinPairing tau P_L ((1 - P_L) * ofStage n X₁) ((1 - P_L) * ofStage n X₁) ≤ 0) ∧
    (peirceMaurerCartanCurvature P_L (ofStage n A₀) (ofStage n C₀) =
      genJ P_L (ofStage n A₀) (ofStage n C₀) + genV P_L (ofStage n A₀) (ofStage n C₀)) ∧
    (peirceCovariantDeriv P_L (ofStage n A₀) (ofStage n C₀)
      (genV P_L (ofStage n A₀) (ofStage n C₀)) = 0) := by
  dsimp only
  have hP_L : ofStage n P₀ * ofStage n P₀ = ofStage n P₀ := map_idempotent (ofStage n) hP₀
  have hP_Ls : star (ofStage n P₀) = ofStage n P₀ := by
    rw [← ofStage_star n P₀, hP₀s]
  have hSplit₀ := cartan_curvature_torsion_graded_split (invS P₀)
    (evenGrade P₀ X₁) (evenGrade P₀ X₂) (evenGrade P₀ dX)
    (genPhi P₀ A₀ C₀) (genPhi P₀ A₂ C₂) (oddGrade P₀ dX)
    (invS_comm_evenGrade hP₀ X₁) (invS_comm_evenGrade hP₀ X₂) (invS_comm_evenGrade hP₀ dX)
    (invS_anticomm_genPhi hP₀ A₀ C₀) (invS_anticomm_genPhi hP₀ A₂ C₂)
    (invS_anticomm_oddGrade hP₀ dX)
  have hBondF : bondMap stageBond n m hnm
      ((evenGrade P₀ dX + oddGrade P₀ dX) +
        PeirceSpine.comm (evenGrade P₀ X₁ + genPhi P₀ A₀ C₀)
          (evenGrade P₀ X₂ + genPhi P₀ A₂ C₂)) =
      (bondMap stageBond n m hnm (evenGrade P₀ dX +
          PeirceSpine.comm (evenGrade P₀ X₁) (evenGrade P₀ X₂)) +
        bondMap stageBond n m hnm (PeirceSpine.comm (genPhi P₀ A₀ C₀) (genPhi P₀ A₂ C₂))) +
      bondMap stageBond n m hnm (oddGrade P₀ dX +
        PeirceSpine.comm (evenGrade P₀ X₁) (genPhi P₀ A₂ C₂) -
        PeirceSpine.comm (evenGrade P₀ X₂) (genPhi P₀ A₀ C₀)) := by
    rw [hSplit₀.1, map_add, map_add]
  have hR : ofStage n (evenGrade P₀ dX + PeirceSpine.comm (evenGrade P₀ X₁) (evenGrade P₀ X₂)) =
      evenGrade (ofStage n P₀) (ofStage n dX) +
        PeirceSpine.comm (evenGrade (ofStage n P₀) (ofStage n X₁))
          (evenGrade (ofStage n P₀) (ofStage n X₂)) := by
    rw [map_add, map_evenGrade, map_comm, map_evenGrade, map_evenGrade]
  have hE : ofStage n (PeirceSpine.comm (genPhi P₀ A₀ C₀) (genPhi P₀ A₂ C₂)) =
      PeirceSpine.comm (genPhi (ofStage n P₀) (ofStage n A₀) (ofStage n C₀))
        (genPhi (ofStage n P₀) (ofStage n A₂) (ofStage n C₂)) := by
    rw [map_comm, map_genPhi, map_genPhi]
  have hT : ofStage n (oddGrade P₀ dX +
        PeirceSpine.comm (evenGrade P₀ X₁) (genPhi P₀ A₂ C₂) -
        PeirceSpine.comm (evenGrade P₀ X₂) (genPhi P₀ A₀ C₀)) =
      oddGrade (ofStage n P₀) (ofStage n dX) +
        PeirceSpine.comm (evenGrade (ofStage n P₀) (ofStage n X₁))
          (genPhi (ofStage n P₀) (ofStage n A₂) (ofStage n C₂)) -
        PeirceSpine.comm (evenGrade (ofStage n P₀) (ofStage n X₂))
          (genPhi (ofStage n P₀) (ofStage n A₀) (ofStage n C₀)) := by
    rw [map_sub, map_add, map_oddGrade, map_comm, map_comm, map_evenGrade, map_evenGrade,
      map_genPhi, map_genPhi]
  have hF : ofStage n ((evenGrade P₀ dX + oddGrade P₀ dX) +
        PeirceSpine.comm (evenGrade P₀ X₁ + genPhi P₀ A₀ C₀)
          (evenGrade P₀ X₂ + genPhi P₀ A₂ C₂)) =
      (evenGrade (ofStage n P₀) (ofStage n dX) + oddGrade (ofStage n P₀) (ofStage n dX)) +
        PeirceSpine.comm (evenGrade (ofStage n P₀) (ofStage n X₁) +
          genPhi (ofStage n P₀) (ofStage n A₀) (ofStage n C₀))
          (evenGrade (ofStage n P₀) (ofStage n X₂) +
            genPhi (ofStage n P₀) (ofStage n A₂) (ofStage n C₂)) := by
    rw [map_add, map_add, map_evenGrade, map_oddGrade, map_comm, map_add, map_add,
      map_evenGrade, map_evenGrade, map_genPhi, map_genPhi]
  have hSplitL := cartan_curvature_torsion_graded_split (invS (ofStage n P₀))
    (evenGrade (ofStage n P₀) (ofStage n X₁)) (evenGrade (ofStage n P₀) (ofStage n X₂))
    (evenGrade (ofStage n P₀) (ofStage n dX))
    (genPhi (ofStage n P₀) (ofStage n A₀) (ofStage n C₀))
    (genPhi (ofStage n P₀) (ofStage n A₂) (ofStage n C₂))
    (oddGrade (ofStage n P₀) (ofStage n dX))
    (invS_comm_evenGrade hP_L _) (invS_comm_evenGrade hP_L _) (invS_comm_evenGrade hP_L _)
    (invS_anticomm_genPhi hP_L _ _) (invS_anticomm_genPhi hP_L _ _)
    (invS_anticomm_oddGrade hP_L _)
  have hLim := limit_krein_polarization_and_self_dual_yang_mills tau htau hP_L hP_Ls
    (ofStage n A₀) (ofStage n C₀) (ofStage n X₁) n hnm P₀ A₀ C₀ X₁
  exact ⟨hBondF, hR, hE, hT, hF, hSplitL.1, hSplitL.2.1, hSplitL.2.2.1,
    hLim.2.2.2.2.1, hLim.2.2.2.2.2.1, hLim.2.2.2.2.2.2.2.1, hLim.2.2.2.2.2.2.2.2.1⟩

/-! ### Part 5: Axial Spin-Torsion Cranking → Machian ZAMO Frame-Dragging → Singlet–Triplet Instability -/

/-- Self-consistent Einstein–Cartan ZAMO frame-dragging frequency induced by the axial
torsion 3-component `S³ = κ_EC J₅³`. -/
def axialTorsionDragFreq (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC : ℝ) : ℝ :=
  κ_EC * diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ 3

private lemma torsion_drag_freq_expand (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC : ℝ) :
    κ_EC * ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 -
        (c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 - d₂ ^ 2) / 2) =
      κ_EC * ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2 - c₁ ^ 2 - d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2) := by
  ring

private lemma torsion_drag_gap_iff (J ω Ω_drag : ℝ) :
    ((1 / 4 : ℝ) * J - (ω - Ω_drag)) - -(3 / 4 : ℝ) * J = J - (ω - Ω_drag) ∧
    (ω < J + Ω_drag ↔ -(3 / 4 : ℝ) * J < (1 / 4 : ℝ) * J - (ω - Ω_drag)) ∧
    (ω = J + Ω_drag ↔ (1 / 4 : ℝ) * J - (ω - Ω_drag) = -(3 / 4 : ℝ) * J) ∧
    (J + Ω_drag < ω ↔ (1 / 4 : ℝ) * J - (ω - Ω_drag) < -(3 / 4 : ℝ) * J) := by
  refine ⟨by ring, ⟨fun h => by linarith [h], fun h => by linarith [h]⟩,
    ⟨fun h => by linarith [h], fun h => by linarith [h]⟩,
    ⟨fun h => by linarith [h], fun h => by linarith [h]⟩⟩

/-- **Theorem 5 (Axial Spin-Torsion → Machian ZAMO Frame-Dragging → Singlet–Triplet Instability)**:
Links `GeometroMagnetoGravityCrankingDirac`, `MachianFrameDraggingBridge`, `CrankingParity`, and
`DoubledMinkowskiRotatingSpinInstability`. -/
theorem axial_spin_torsion_zamo_frame_dragging_singlet_triplet_capstone
    (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC J ω μ₀ lam ρ ρ_star : ℝ) :
    let J₅ := diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let S : Fin 4 → ℝ := fun μ => κ_EC * J₅ μ
    let Ω₁ := diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω₂ := diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω_drag := axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC
    let H := frameDraggedSpinHamiltonian J ω Ω_drag
    let E_S := -(3 / 4 : ℝ) * J
    let E_T1 := (1 / 4 : ℝ) * J - (ω - Ω_drag)
    let E_Tm1 := (1 / 4 : ℝ) * J + (ω - Ω_drag)
    (-minkPair S J₅ = κ_EC * (Ω₁ ^ 2 + Ω₂ ^ 2)) ∧
    (Ω_drag = κ_EC *
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2 - c₁ ^ 2 - d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2)) ∧
    (Matrix.toLin' H =
      routhian (Matrix.toLin' ((J / 4 : ℝ) • spinExchange4))
        (Matrix.toLin' totalSpinZ4) (ω - Ω_drag)) ∧
    (H.mulVec singletState = E_S • singletState) ∧
    (H.mulVec tripletPlusState = E_T1 • tripletPlusState) ∧
    (H.mulVec tripletMinusState = E_Tm1 • tripletMinusState) ∧
    (E_T1 - E_S = J - (ω - Ω_drag)) ∧
    (ω < J + Ω_drag ↔ E_S < E_T1) ∧
    (ω = J + Ω_drag ↔ E_T1 = E_S) ∧
    (J + Ω_drag < ω ↔ E_T1 < E_S) ∧
    (E_Tm1 - E_T1 = 2 * (ω - Ω_drag)) ∧
    (ω = Ω_drag → E_T1 - E_S = J ∧ E_Tm1 - E_S = J) ∧
    (μ₀ ^ 2 < (ω - Ω_drag) ^ 2 → 0 < lam →
      ρ_star ^ 2 = ((ω - Ω_drag) ^ 2 - μ₀ ^ 2) / lam →
      crankedDiracVacuumPot μ₀ (ω - Ω_drag) lam ρ_star ≤
        crankedDiracVacuumPot μ₀ (ω - Ω_drag) lam ρ ∧
      crankedDiracVacuumPot μ₀ (ω - Ω_drag) lam ρ_star <
        crankedDiracVacuumPot μ₀ (ω - Ω_drag) lam 0) := by
  dsimp only
  have hFKR := fierz_kofink_rodichev_chiral_null_current_identities
    a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC
  have hDrag : axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC =
      κ_EC * ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2 - c₁ ^ 2 - d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2) := by
    unfold axialTorsionDragFreq diracAxialCurrent chiralNullCurrent
    simpa using torsion_drag_freq_expand a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC
  have hInst := real_rotating_frame_singlet_triplet_instability J
    (ω - axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC)
  have hZamo := zamo_triplet_zeeman_splitting_cancellation J ω
    (axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC)
  have hRouth := frameDraggedSpinHamiltonian_eq_cranking_routhian J ω
    (axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC)
  have hGap := torsion_drag_gap_iff J ω (axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC)
  refine ⟨hFKR.2.2.2.2, hDrag, hRouth, hInst.2.1, hZamo.1, hZamo.2.1,
    hGap.1, hGap.2.1, hGap.2.2.1, hGap.2.2.2, hZamo.2.2.1, hZamo.2.2.2.2, ?_⟩
  intro hCrank hLam hStar
  have hYT := yvon_takabayasi_chiral_invariance_and_cranked_vacuum_condensation
    (diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂)
    (diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂)
    0 μ₀ (ω - axialTorsionDragFreq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC) lam ρ ρ_star
    hCrank hLam hStar
  exact ⟨hYT.2.2.2.1, hYT.2.2.2.2.2⟩

end PeirceColimitBridge

end InfoGeometry.Canonical.DoubledMinkowskiSpinToGravityCapstone
