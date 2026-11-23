/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import InfoGeometry.Algebra.GradedNullconeAlgebra
import InfoGeometry.Clifford.DaviauRealDirac8x8
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import InfoGeometry.Clifford.DeBroglieDaviauPhotonProcaFusion

/-!
# Daviau–Lochak Differential Derivations, Chiral/Electric Gauge Rotation, and Cartan Soldering

Extends the Daviau–Lochak–Bertrand real 8D Dirac formalization with four operational
differential-algebraic bridges:

1. **Part A (`FusionDerivConfig`, `expDeriv`, `planeWaveFusionConfig`)**:
   upgrades `DeBroglieDaviauPhotonProcaFusion` from manual derivative arrays `(da, db)` to four
   genuine `RingDeriv R` derivations satisfying Leibniz's rule on composite photon-Proca
   bilinear fields, with a concrete nontrivial massive plane-wave solution over
   `AddMonoidAlgebra ℝ ℝ`.
2. **Part B (`chiralGaugeMat`, `electricGaugeMat`, `lochak_chiral_gauge_action`,
   `daviau_electric_gauge_invariance`)**:
   proves that Lochak's chiral gauge `exp(α Γ⁰¹²³)` rotates `(Ω₁, Ω₂)` by `2α` while preserving
   `Ω₁² + Ω₂²`, `J^μ`, and `Σ^μ`, whereas Daviau's electric gauge `exp(α P₃)` leaves all four
   densities invariant.
3. **Part C (`mat8RingDeriv`, `trigGaugeUnit_logSoldering`, `SmoothRealFun`)**:
   lifts scalar ring derivations entrywise to `M₈(R)`, evaluates the exact Cartan soldering form
   `logSoldering (mat8RingDeriv d) g = g⁻¹ * d(g) = θ' • J` over both abstract differential rings
   and the smooth differential ring `SmoothRealFun = C^∞(ℝ, ℝ)` using `Real.cos` / `Real.sin`.
4. **Part D (`chiral_soldering_matches_rodichev_torsion`)**:
   matches the chiral logarithmic soldering connection `-½ σ_ν Γ⁰¹²³` onto Rodichev's skew-torsion
   Dirac term (`rodichev_chiral_torsion_dirac_term`).
-/

noncomputable section

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Canonical.KreinMajoranaBlockInvariance hiding Mat8R Vec8R
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.LochakRodichevFierzKrein
open InfoGeometry.Clifford.DeBroglieDaviauPhotonProcaFusion

namespace InfoGeometry.Clifford.DaviauLochakDifferentialGauge

/-! ### Trap T16 Noncommutativity Guards -/

/-- Explicit Trap T16 noncommutativity witness for `M₈(ℝ)`. -/
theorem mat8R_mul_noncomm_witness :
    ∃ A B : Mat8R, A * B ≠ B * A :=
  ⟨gammaR 0, gammaR 1, daviau_mat8_noncomm.1⟩

/-- Explicit Trap T16 noncommutativity witness for `M₈(R)` over any nontrivial ring `R`. -/
theorem mat8Ring_mul_noncomm_witness (R : Type*) [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 8) (Fin 8) R, A * B ≠ B * A := by
  let e01 : Matrix (Fin 8) (Fin 8) R := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let e11 : Matrix (Fin 8) (Fin 8) R := Matrix.of fun i j => if i = 1 ∧ j = 1 then 1 else 0
  refine ⟨e01, e11, ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 8) (Fin 8) R => M 0 1) h
  rw [Matrix.mul_apply, Matrix.mul_apply] at h01
  simp [e01, e11] at h01

/-! ### Part 0: Generic `RingDeriv` Calculus Helpers -/

section RingDerivHelpers

variable {E : Type*} [Ring E] (D : RingDeriv E)

@[simp]
theorem ringDeriv_zero : D 0 = 0 := by
  have h : D (0 + 0) = D 0 + D 0 := D.map_add 0 0
  rw [add_zero] at h
  have h2 := congrArg (fun x => x - D 0) h
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

@[simp]
theorem ringDeriv_neg (x : E) : D (-x) = -D x := by
  have h : D (-x + x) = D (-x) + D x := D.map_add (-x) x
  rw [neg_add_cancel, ringDeriv_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

@[simp]
theorem ringDeriv_sub (x y : E) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, ringDeriv_neg, sub_eq_add_neg]

theorem ringDeriv_natCast : ∀ n : ℕ, D (n : E) = 0
  | 0 => by simp
  | n + 1 => by rw [Nat.cast_succ, D.map_add, ringDeriv_natCast n, D.map_one, add_zero]

@[simp]
theorem ringDeriv_intCast (z : ℤ) : D (z : E) = 0 := by
  cases z with
  | ofNat n => simpa using ringDeriv_natCast D n
  | negSucc n =>
    rw [Int.cast_negSucc, ringDeriv_neg, ringDeriv_natCast D (n + 1), neg_zero]

theorem ringDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → E) :
    D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, D.map_add, ih, Finset.sum_insert has]

end RingDerivHelpers

/-! ### Part A: `RingDeriv` Upgrade of `DeBroglieDaviauPhotonProcaFusion` & Plane-Wave Witness -/

/-- Photon–Proca fusion configuration driven by four `RingDeriv R` differential operators `∂_μ`. -/
structure FusionDerivConfig (R : Type*) [CommRing R] where
  a : Fin 4 → R
  b : Fin 4 → R
  halfMass : R
  deriv : Fin 4 → RingDeriv R

instance : Inhabited (FusionDerivConfig ℝ) :=
  ⟨⟨0, 0, 0, fun _ => innerRingDeriv 0⟩⟩

/-- Underlying `FusionJetData R` induced by applying `C.deriv μ` to the chiral spinor fields. -/
def FusionDerivConfig.toJet {R : Type*} [CommRing R] (C : FusionDerivConfig R) :
    FusionJetData R where
  a := C.a
  b := C.b
  da μ j := C.deriv μ (C.a j)
  db μ j := C.deriv μ (C.b j)
  halfMass := C.halfMass

section FusionDerivBridge

variable {R : Type*} [CommRing R] (C : FusionDerivConfig R)

private lemma deriv_prod_eq (μ j k : Fin 4) :
    C.deriv μ (C.a j * C.b k) = dProd C.toJet μ j k := by
  rw [(C.deriv μ).map_mul, add_comm]
  rfl

theorem deriv_photonA (μ ν : Fin 4) :
    C.deriv μ (photonA C.toJet ν) = dPhotonA C.toJet μ ν := by
  fin_cases ν <;>
    · simp only [photonA, dPhotonA, FusionDerivConfig.toJet, dProd,
        RingDeriv.map_add, ringDeriv_sub, ringDeriv_neg, RingDeriv.map_mul]
      ring

theorem deriv_photonFBase (ρ μ ν : Fin 4) :
    C.deriv ρ (photonFBase C.toJet μ ν) = dPhotonFBase C.toJet ρ μ ν := by
  fin_cases μ <;> fin_cases ν <;>
    (simp [photonFBase, dPhotonFBase, FusionDerivConfig.toJet, dProd,
      RingDeriv.map_add, RingDeriv.map_mul] <;> try ring)

theorem deriv_photonF (hm : ∀ ρ : Fin 4, C.deriv ρ C.halfMass = 0) (ρ μ ν : Fin 4) :
    C.deriv ρ (photonF C.toJet μ ν) = dPhotonF C.toJet ρ μ ν := by
  have hm2 : C.deriv ρ (photonMass C.toJet) = 0 := by
    change C.deriv ρ ((2 : R) * C.halfMass) = 0
    rw [(C.deriv ρ).map_mul, hm ρ, mul_zero, zero_add]
    have h2 : C.deriv ρ ((2 : ℕ) : R) = 0 := ringDeriv_natCast (C.deriv ρ) 2
    simpa using congrArg (· * C.halfMass) h2
  dsimp [photonF, dPhotonF]
  rw [(C.deriv ρ).map_mul, hm2, zero_mul, add_zero, deriv_photonFBase]

theorem deriv_fusionScalarS (μ : Fin 4) :
    C.deriv μ (fusionScalarS C.toJet) = dFusionS C.toJet μ := by
  dsimp [fusionScalarS, dFusionS, FusionDerivConfig.toJet, dProd]
  simp only [RingDeriv.map_add, RingDeriv.map_mul]
  ring

theorem deriv_fusionPseudoscalarP (μ : Fin 4) :
    C.deriv μ (fusionPseudoscalarP C.toJet) = dFusionP C.toJet μ := by
  dsimp [fusionPseudoscalarP, dFusionP, FusionDerivConfig.toJet, dProd]
  simp only [RingDeriv.map_add, ringDeriv_sub, RingDeriv.map_mul]
  ring

theorem deriv_fusionAxialB (μ ν : Fin 4) :
    C.deriv μ (fusionAxialB C.toJet ν) = dFusionB C.toJet μ ν := by
  fin_cases ν <;>
    · simp only [fusionAxialB, dFusionB, FusionDerivConfig.toJet, dProd,
        RingDeriv.map_add, ringDeriv_sub, RingDeriv.map_mul]
      ring

/-- **De Broglie–Daviau Photon–Proca Fusion Theorem with Genuine `RingDeriv` Operators**:
all seven Maxwell–Proca and non-Maxwellian identities follow from Leibniz's rule on composite
chiral bilinears under spacetime motion lock (`Eq. 68`), left/right chiral Dirac equations
(`Eqs. 69–70`), and constant mass (`∂_ρ halfMass = 0`). -/
theorem deBroglie_daviau_ringDeriv_fusion
    (h68 : IsMotionLocked C.toJet) (h69 : SatisfiesLeftChiralEq C.toJet)
    (h70 : SatisfiesRightChiralEq C.toJet) (hm : ∀ ρ : Fin 4, C.deriv ρ C.halfMass = 0) :
    (∀ μ ν : Fin 4,
      photonF C.toJet μ ν = C.deriv μ (photonA C.toJet ν) - C.deriv ν (photonA C.toJet μ)) ∧
    (∀ ν : Fin 4,
      C.deriv 0 (photonF C.toJet 0 ν) - C.deriv 1 (photonF C.toJet 1 ν) -
        C.deriv 2 (photonF C.toJet 2 ν) - C.deriv 3 (photonF C.toJet 3 ν) =
        -(photonMass C.toJet ^ 2) * photonA C.toJet ν) ∧
    (C.deriv 0 (photonA C.toJet 0) - C.deriv 1 (photonA C.toJet 1) -
        C.deriv 2 (photonA C.toJet 2) - C.deriv 3 (photonA C.toJet 3) = 0) ∧
    (∀ ρ μ ν : Fin 4,
      C.deriv ρ (photonF C.toJet μ ν) + C.deriv μ (photonF C.toJet ν ρ) +
        C.deriv ν (photonF C.toJet ρ μ) = 0) ∧
    (∀ μ : Fin 4, C.deriv μ (fusionPseudoscalarP C.toJet) = 0) ∧
    (∀ μ : Fin 4, C.deriv μ (fusionScalarS C.toJet) =
        -photonMass C.toJet * fusionAxialB C.toJet μ) ∧
    (C.deriv 0 (fusionAxialB C.toJet 0) - C.deriv 1 (fusionAxialB C.toJet 1) -
        C.deriv 2 (fusionAxialB C.toJet 2) - C.deriv 3 (fusionAxialB C.toJet 3) =
        photonMass C.toJet * fusionScalarS C.toJet) := by
  have hbase := deBroglie_daviau_real_photon_proca_fusion C.toJet h68 h69 h70
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ ν
    rw [deriv_photonA, deriv_photonA]
    exact hbase.1 μ ν
  · intro ν
    simp_rw [deriv_photonF C hm]
    exact hbase.2.1 ν
  · simp_rw [deriv_photonA]
    exact hbase.2.2.1
  · intro ρ μ ν
    simp_rw [deriv_photonF C hm]
    exact hbase.2.2.2.1 ρ μ ν
  · intro μ
    rw [deriv_fusionPseudoscalarP]
    exact hbase.2.2.2.2.1 μ
  · intro μ
    rw [deriv_fusionScalarS]
    exact hbase.2.2.2.2.2.1 μ
  · simp_rw [deriv_fusionAxialB]
    exact hbase.2.2.2.2.2.2

end FusionDerivBridge

private lemma expDeriv_fun_sum_add (w : ℝ) (f g : AddMonoidAlgebra ℝ ℝ) :
    (f + g).coeff.sum (fun freq c => AddMonoidAlgebra.single freq ((w * freq) * c)) =
      f.coeff.sum (fun freq c => AddMonoidAlgebra.single freq ((w * freq) * c)) +
        g.coeff.sum (fun freq c => AddMonoidAlgebra.single freq ((w * freq) * c)) := by
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => by simp)
    (fun freq c₁ c₂ => by rw [mul_add, ← AddMonoidAlgebra.single_add])

private lemma expDeriv_fun_single (w freq c : ℝ) :
    (AddMonoidAlgebra.single freq c).coeff.sum
        (fun k d => AddMonoidAlgebra.single k ((w * k) * d)) =
      AddMonoidAlgebra.single freq ((w * freq) * c) := by
  simp only [AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

/-- Concrete frequency-weighted derivation `∂_w (single freq c) = single freq ((w * freq) * c)`
on the real exponential group algebra `AddMonoidAlgebra ℝ ℝ`. -/
def expDeriv (w : ℝ) : RingDeriv (AddMonoidAlgebra ℝ ℝ) where
  toFun f := f.coeff.sum fun freq c => AddMonoidAlgebra.single freq ((w * freq) * c)
  map_add' := expDeriv_fun_sum_add w
  map_mul' f g := by
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ =>
      rw [add_mul, expDeriv_fun_sum_add, hf₁, hf₂, expDeriv_fun_sum_add, add_mul, add_mul]
      abel
    | single freq₁ c₁ =>
      induction g using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ =>
        rw [mul_add, expDeriv_fun_sum_add, hg₁, hg₂, expDeriv_fun_sum_add, mul_add, mul_add]
        abel
      | single freq₂ c₂ =>
        rw [AddMonoidAlgebra.single_mul_single, expDeriv_fun_single, expDeriv_fun_single,
          expDeriv_fun_single, AddMonoidAlgebra.single_mul_single,
          AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.single_add]
        congr 1
        ring

@[simp]
theorem expDeriv_single (w freq c : ℝ) :
    expDeriv w (AddMonoidAlgebra.single freq c) =
      AddMonoidAlgebra.single freq ((w * freq) * c) :=
  expDeriv_fun_single w freq c

@[simp]
private lemma expDeriv_toFun_single (w freq c : ℝ) :
    (expDeriv w).toFun (AddMonoidAlgebra.single freq c) =
      AddMonoidAlgebra.single freq ((w * freq) * c) :=
  expDeriv_fun_single w freq c

/-- Nontrivial massive plane-wave `FusionDerivConfig` over `AddMonoidAlgebra ℝ ℝ` at half-mass `m`
with wavevector `(0, 0, -m, 0)` acting on the exponential mode `single 1 1`. -/
def planeWaveFusionConfig (m : ℝ) : FusionDerivConfig (AddMonoidAlgebra ℝ ℝ) where
  a := ![AddMonoidAlgebra.single 1 1, 0, 0, 0]
  b := ![AddMonoidAlgebra.single 1 1, 0, 0, 0]
  halfMass := AddMonoidAlgebra.single 0 m
  deriv μ := expDeriv ((![0, 0, -m, 0] : Fin 4 → ℝ) μ)

/-- Concrete nontrivial witness certifying `deBroglie_daviau_ringDeriv_fusion`: for every `m ≠ 0`,
`planeWaveFusionConfig m` satisfies motion lock (`Eq. 68`), left/right chiral equations (`Eqs. 69–70`),
constant mass, and nonzero photon mass, gauge potential, field strength, scalar density, and scalar
gradient. -/
theorem planeWaveFusionConfig_satisfies_all (m : ℝ) (hm0 : m ≠ 0) :
    IsMotionLocked (planeWaveFusionConfig m).toJet ∧
    SatisfiesLeftChiralEq (planeWaveFusionConfig m).toJet ∧
    SatisfiesRightChiralEq (planeWaveFusionConfig m).toJet ∧
    (∀ ρ : Fin 4, (planeWaveFusionConfig m).deriv ρ (planeWaveFusionConfig m).halfMass = 0) ∧
    photonMass (planeWaveFusionConfig m).toJet ≠ 0 ∧
    photonA (planeWaveFusionConfig m).toJet 1 ≠ 0 ∧
    photonF (planeWaveFusionConfig m).toJet 2 1 ≠ 0 ∧
    fusionScalarS (planeWaveFusionConfig m).toJet ≠ 0 ∧
    (planeWaveFusionConfig m).deriv 2 (fusionScalarS (planeWaveFusionConfig m).toJet) ≠ 0 := by
  have hm_const : ∀ ρ : Fin 4,
      (planeWaveFusionConfig m).deriv ρ (planeWaveFusionConfig m).halfMass = 0 := by
    intro ρ
    dsimp [planeWaveFusionConfig]
    simp
  have h68 : IsMotionLocked (planeWaveFusionConfig m).toJet := by
    intro μ j k
    fin_cases μ <;> fin_cases j <;> fin_cases k <;>
      simp [planeWaveFusionConfig, FusionDerivConfig.toJet]
  have h69 : SatisfiesLeftChiralEq (planeWaveFusionConfig m).toJet := by
    dsimp [SatisfiesLeftChiralEq, planeWaveFusionConfig, FusionDerivConfig.toJet]
    simp [AddMonoidAlgebra.single_mul_single]
  have h70 : SatisfiesRightChiralEq (planeWaveFusionConfig m).toJet := by
    dsimp [SatisfiesRightChiralEq, planeWaveFusionConfig, FusionDerivConfig.toJet]
    simp [AddMonoidAlgebra.single_mul_single]
  have hmass_ne : photonMass (planeWaveFusionConfig m).toJet ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : AddMonoidAlgebra ℝ ℝ => f.coeff 0) h
    simp [photonMass, planeWaveFusionConfig, FusionDerivConfig.toJet, two_mul,
      AddMonoidAlgebra.coeff_add] at h0
    exact hm0 (by linarith)
  have hA1_ne : photonA (planeWaveFusionConfig m).toJet 1 ≠ 0 := by
    intro h
    have h2 := congrArg (fun f : AddMonoidAlgebra ℝ ℝ => f.coeff 2) h
    simp [photonA, planeWaveFusionConfig, FusionDerivConfig.toJet,
      AddMonoidAlgebra.single_mul_single] at h2
    norm_num at h2
  have hF21_ne : photonF (planeWaveFusionConfig m).toJet 2 1 ≠ 0 := by
    intro h
    have h2 := congrArg (fun f : AddMonoidAlgebra ℝ ℝ => f.coeff 2) h
    simp [photonF, photonFBase, photonMass, planeWaveFusionConfig, FusionDerivConfig.toJet,
      two_mul, mul_neg, add_mul, AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.coeff_add] at h2
    norm_num at h2
    exact hm0 (by linarith)
  have hS_eq : fusionScalarS (planeWaveFusionConfig m).toJet = AddMonoidAlgebra.single (2 : ℝ) 1 := by
    simp [fusionScalarS, planeWaveFusionConfig, FusionDerivConfig.toJet,
      AddMonoidAlgebra.single_mul_single]
    congr 1
    norm_num
  have hS_ne : fusionScalarS (planeWaveFusionConfig m).toJet ≠ 0 := by
    intro h
    rw [hS_eq] at h
    have h2 := congrArg (fun f : AddMonoidAlgebra ℝ ℝ => f.coeff 2) h
    simp at h2
  have hdS_ne :
      (planeWaveFusionConfig m).deriv 2 (fusionScalarS (planeWaveFusionConfig m).toJet) ≠ 0 := by
    intro h
    have hderiv :
        (planeWaveFusionConfig m).deriv 2 (AddMonoidAlgebra.single (2 : ℝ) 1) =
          AddMonoidAlgebra.single (2 : ℝ) ((-m * 2) * 1) := by
      dsimp [planeWaveFusionConfig]
      exact expDeriv_toFun_single (-m) 2 1
    rw [hS_eq, hderiv] at h
    have h2 := congrArg (fun f : AddMonoidAlgebra ℝ ℝ => f.coeff 2) h
    simp at h2
    exact hm0 (by linarith)
  exact ⟨h68, h69, h70, hm_const, hmass_ne, hA1_ne, hF21_ne, hS_ne, hdS_ne⟩

/-! ### Part B: Lochak Chiral Gauge `exp(α Γ⁰¹²³)` vs. Daviau Electric Gauge `exp(α P₃)` -/

private theorem trig_sq_unit_prod {R E : Type*} [CommRing R] [Ring E] [Algebra R E]
    (J : E) (hJ2 : J * J = -1) (a b c d : R) :
    (a • (1 : E) + b • J) * (c • (1 : E) + d • J) =
      (a * c - b * d) • (1 : E) + (a * d + b * c) • J := by
  have h11 : (a • (1 : E)) * (c • (1 : E)) = (a * c) • (1 : E) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]
  have h1J : (a • (1 : E)) * (d • J) = (a * d) • J := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]
  have hJ1 : (b • J) * (c • (1 : E)) = (b * c) • J := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one]
  have hJJ : (b • J) * (d • J) = -((b * d) • (1 : E)) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hJ2, smul_neg]
  rw [add_mul, mul_add, mul_add, h11, h1J, hJ1, hJJ, sub_smul, add_smul]
  abel

/-- Lochak chiral gauge operator `U(α) = cos(α) I₈ + sin(α) Γ⁰¹²³` in `M₈(ℝ)`. -/
def chiralGaugeMat (α : ℝ) : Mat8R :=
  Real.cos α • (1 : Mat8R) + Real.sin α • gamma0123R

/-- Daviau electric `U(1)` gauge operator `E(α) = cos(α) I₈ + sin(α) P₃` in `M₈(ℝ)`. -/
def electricGaugeMat (α : ℝ) : Mat8R :=
  Real.cos α • (1 : Mat8R) + Real.sin α • quatPR 2

theorem chiralGaugeMat_mul (α β : ℝ) :
    chiralGaugeMat α * chiralGaugeMat β = chiralGaugeMat (α + β) := by
  dsimp [chiralGaugeMat]
  rw [trig_sq_unit_prod gamma0123R gamma0123R_sq, Real.cos_add, Real.sin_add,
    add_comm (Real.sin α * Real.cos β)]

theorem chiralGaugeMat_zero : chiralGaugeMat 0 = (1 : Mat8R) := by
  simp [chiralGaugeMat]

/-- Unit element `chiralGaugeUnit α : Mat8Rˣ` with `(chiralGaugeUnit α)⁻¹ = chiralGaugeUnit (-α)`. -/
def chiralGaugeUnit (α : ℝ) : Mat8Rˣ where
  val := chiralGaugeMat α
  inv := chiralGaugeMat (-α)
  val_inv := by rw [chiralGaugeMat_mul, add_neg_cancel, chiralGaugeMat_zero]
  inv_val := by rw [chiralGaugeMat_mul, neg_add_cancel, chiralGaugeMat_zero]

theorem electricGaugeMat_mul (α β : ℝ) :
    electricGaugeMat α * electricGaugeMat β = electricGaugeMat (α + β) := by
  dsimp [electricGaugeMat]
  rw [trig_sq_unit_prod (quatPR 2) (quatPR_sq 2), Real.cos_add, Real.sin_add,
    add_comm (Real.sin α * Real.cos β)]

theorem electricGaugeMat_zero : electricGaugeMat 0 = (1 : Mat8R) := by
  simp [electricGaugeMat]

/-- Unit element `electricGaugeUnit α : Mat8Rˣ` with inverse `electricGaugeUnit (-α)`. -/
def electricGaugeUnit (α : ℝ) : Mat8Rˣ where
  val := electricGaugeMat α
  inv := electricGaugeMat (-α)
  val_inv := by rw [electricGaugeMat_mul, add_neg_cancel, electricGaugeMat_zero]
  inv_val := by rw [electricGaugeMat_mul, neg_add_cancel, electricGaugeMat_zero]

private lemma gamma0123Z_transpose_mul_gamma0 :
    gamma0123Zᵀ * gamma0Z = gamma0Z * gamma0123Z := by
  decide

theorem gamma0123R_transpose_mul_gamma0 :
    gamma0123Rᵀ * gammaR 0 = gammaR 0 * gamma0123R := by
  change (castZ8 gamma0123Z)ᵀ * castZ8 gamma0Z = castZ8 gamma0Z * castZ8 gamma0123Z
  rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, gamma0123Z_transpose_mul_gamma0]

private lemma omega1_eq_dot_gamma0 (Φ : Vec8R) :
    omega1 Φ = dotProduct Φ ((gammaR 0) *ᵥ Φ) := by
  change dotProduct Φ (kreinMetric8 *ᵥ Φ) = dotProduct Φ ((gammaR 0) *ᵥ Φ)
  rw [gamma0R_eq_kreinMetric8]

private lemma omega2_eq_dot_gamma0 (Φ : Vec8R) :
    omega2 Φ = dotProduct Φ ((gammaR 0 * gamma0123R) *ᵥ Φ) := by
  change dotProduct Φ (kreinMetric8 *ᵥ (gamma0123R *ᵥ Φ)) =
    dotProduct Φ ((gammaR 0 * gamma0123R) *ᵥ Φ)
  rw [gamma0R_eq_kreinMetric8, Matrix.mulVec_mulVec]

private lemma electricCurrentJ_eq_dot_gamma0 (Φ : Vec8R) (μ : Fin 4) :
    electricCurrentJ Φ μ = dotProduct Φ ((gammaR 0 * gammaR μ) *ᵥ Φ) := by
  change dotProduct Φ (kreinMetric8 *ᵥ ((gammaR μ) *ᵥ Φ)) =
    dotProduct Φ ((gammaR 0 * gammaR μ) *ᵥ Φ)
  rw [gamma0R_eq_kreinMetric8, Matrix.mulVec_mulVec]

private lemma axialCurrentSigma_eq_dot_gamma0 (Φ : Vec8R) (μ : Fin 4) :
    axialCurrentSigma Φ μ =
      dotProduct Φ ((gammaR 0 * (gammaR μ * gamma5Real ⟨2, by decide⟩)) *ᵥ Φ) := by
  change dotProduct Φ (kreinMetric8 *ᵥ ((gammaR μ * gamma5Real ⟨2, by decide⟩) *ᵥ Φ)) =
    dotProduct Φ ((gammaR 0 * (gammaR μ * gamma5Real ⟨2, by decide⟩)) *ᵥ Φ)
  rw [gamma0R_eq_kreinMetric8, Matrix.mulVec_mulVec]

private lemma dot_gamma0_mulVec (A X : Mat8R) (Φ : Vec8R) :
    dotProduct (A *ᵥ Φ) ((gammaR 0 * X) *ᵥ (A *ᵥ Φ)) =
      dotProduct Φ ((Aᵀ * gammaR 0 * (X * A)) *ᵥ Φ) := by
  calc
    dotProduct (A *ᵥ Φ) ((gammaR 0 * X) *ᵥ (A *ᵥ Φ))
        = (Φ ᵥ* Aᵀ) ⬝ᵥ ((gammaR 0 * X) *ᵥ (A *ᵥ Φ)) := by
            rw [← Matrix.vecMul_transpose]
    _ = Φ ⬝ᵥ (Aᵀ *ᵥ ((gammaR 0 * X) *ᵥ (A *ᵥ Φ))) := by
            exact (Matrix.dotProduct_mulVec Φ Aᵀ ((gammaR 0 * X) *ᵥ (A *ᵥ Φ))).symm
    _ = Φ ⬝ᵥ ((Aᵀ * (gammaR 0 * X) * A) *ᵥ Φ) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Φ ⬝ᵥ ((Aᵀ * gammaR 0 * (X * A)) *ᵥ Φ) := by
            simp only [Matrix.mul_assoc]

private lemma dot_gamma0_id_mulVec (A : Mat8R) (Φ : Vec8R) :
    dotProduct (A *ᵥ Φ) ((gammaR 0) *ᵥ (A *ᵥ Φ)) =
      dotProduct Φ ((Aᵀ * gammaR 0 * A) *ᵥ Φ) := by
  simpa [Matrix.mul_one, Matrix.one_mul] using dot_gamma0_mulVec A (1 : Mat8R) Φ

private lemma dotProduct_smul_add (a b : ℝ) (A B : Mat8R) (Φ : Vec8R) :
    dotProduct Φ ((a • A + b • B) *ᵥ Φ) =
      a * dotProduct Φ (A *ᵥ Φ) + b * dotProduct Φ (B *ᵥ Φ) := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]

private lemma chiralGaugeMat_transpose_gamma0 (α : ℝ) :
    (chiralGaugeMat α)ᵀ * gammaR 0 = gammaR 0 * chiralGaugeMat α := by
  dsimp [chiralGaugeMat]
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.add_mul, Matrix.mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
    gamma0123R_transpose_mul_gamma0]

private lemma chiralGaugeMat_conj_anticomm {X : Mat8R}
    (hanti : gamma0123R * X = -(X * gamma0123R)) (α : ℝ) :
    chiralGaugeMat α * X * chiralGaugeMat α = X := by
  dsimp [chiralGaugeMat]
  have h1 : (Real.cos α • (1 : Mat8R) + Real.sin α • gamma0123R) * X =
      X * (Real.cos α • (1 : Mat8R) - Real.sin α • gamma0123R) := by
    rw [Matrix.add_mul, Matrix.mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hanti,
      smul_neg, sub_eq_add_neg]
  rw [h1, Matrix.mul_assoc]
  have h2 : (Real.cos α • (1 : Mat8R) - Real.sin α • gamma0123R) *
      (Real.cos α • (1 : Mat8R) + Real.sin α • gamma0123R) = (1 : Mat8R) := by
    rw [sub_eq_add_neg, ← neg_smul, trig_sq_unit_prod gamma0123R gamma0123R_sq]
    have hcs : Real.cos α * Real.cos α - (-Real.sin α) * Real.sin α = 1 := by
      simpa [sq, sub_eq_add_neg] using Real.cos_sq_add_sin_sq α
    have h0 : Real.cos α * Real.sin α + (-Real.sin α) * Real.cos α = 0 := by ring
    rw [hcs, h0, zero_smul, one_smul, add_zero]
  rw [h2, Matrix.mul_one]

/-- **Lochak Chiral Gauge Theorem (Lochak Eqs. 21–36 / Daviau Eq. 25)**:
under the chiral gauge transformation `Φ ↦ (cos α I₈ + sin α Γ⁰¹²³) Φ`:
- the scalar and pseudoscalar rotate by double angle `2α`:
  `Ω₁' = cos(2α) Ω₁ + sin(2α) Ω₂`, `Ω₂' = -sin(2α) Ω₁ + cos(2α) Ω₂`;
- the Takabayasi–Fierz norm `Ω₁² + Ω₂²` is strictly invariant;
- the electric current `J^μ` and axial current `Σ^μ` are invariant for all `μ : Fin 4`. -/
theorem lochak_chiral_gauge_action (α : ℝ) (Φ : Vec8R) :
    omega1 (chiralGaugeMat α *ᵥ Φ) = Real.cos (2 * α) * omega1 Φ + Real.sin (2 * α) * omega2 Φ ∧
    omega2 (chiralGaugeMat α *ᵥ Φ) = -Real.sin (2 * α) * omega1 Φ + Real.cos (2 * α) * omega2 Φ ∧
    omega1 (chiralGaugeMat α *ᵥ Φ) ^ 2 + omega2 (chiralGaugeMat α *ᵥ Φ) ^ 2 =
      omega1 Φ ^ 2 + omega2 Φ ^ 2 ∧
    (∀ μ : Fin 4, electricCurrentJ (chiralGaugeMat α *ᵥ Φ) μ = electricCurrentJ Φ μ) ∧
    (∀ μ : Fin 4, axialCurrentSigma (chiralGaugeMat α *ᵥ Φ) μ = axialCurrentSigma Φ μ) := by
  have h1 : omega1 (chiralGaugeMat α *ᵥ Φ) =
      Real.cos (2 * α) * omega1 Φ + Real.sin (2 * α) * omega2 Φ := by
    rw [omega1_eq_dot_gamma0, omega1_eq_dot_gamma0, omega2_eq_dot_gamma0, dot_gamma0_id_mulVec,
      chiralGaugeMat_transpose_gamma0, Matrix.mul_assoc, chiralGaugeMat_mul, ← two_mul]
    dsimp [chiralGaugeMat]
    rw [Matrix.mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm, Matrix.mul_one,
      dotProduct_smul_add]
  have h2 : omega2 (chiralGaugeMat α *ᵥ Φ) =
      -Real.sin (2 * α) * omega1 Φ + Real.cos (2 * α) * omega2 Φ := by
    rw [omega2_eq_dot_gamma0, omega1_eq_dot_gamma0, omega2_eq_dot_gamma0, dot_gamma0_mulVec,
      chiralGaugeMat_transpose_gamma0]
    have hcomm : chiralGaugeMat α * gamma0123R = gamma0123R * chiralGaugeMat α := by
      dsimp [chiralGaugeMat]
      rw [Matrix.add_mul, Matrix.mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
    have hsq : gamma0123R * chiralGaugeMat (2 * α) =
        (-Real.sin (2 * α)) • (1 : Mat8R) + Real.cos (2 * α) • gamma0123R := by
      dsimp [chiralGaugeMat]
      rw [Matrix.mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm, Matrix.mul_one,
        gamma0123R_sq, smul_neg, ← neg_smul, add_comm]
    have hmat :
        gammaR 0 * chiralGaugeMat α * (gamma0123R * chiralGaugeMat α) =
          (-Real.sin (2 * α)) • gammaR 0 + Real.cos (2 * α) • (gammaR 0 * gamma0123R) := by
      calc
        gammaR 0 * chiralGaugeMat α * (gamma0123R * chiralGaugeMat α)
            = gammaR 0 * ((chiralGaugeMat α * gamma0123R) * chiralGaugeMat α) := by
                simp only [Matrix.mul_assoc]
        _ = gammaR 0 * (gamma0123R * (chiralGaugeMat α * chiralGaugeMat α)) := by
                rw [hcomm, Matrix.mul_assoc]
        _ = gammaR 0 * (gamma0123R * chiralGaugeMat (2 * α)) := by
                rw [chiralGaugeMat_mul, ← two_mul]
        _ = gammaR 0 * ((-Real.sin (2 * α)) • (1 : Mat8R) + Real.cos (2 * α) • gamma0123R) := by
                rw [hsq]
        _ = (-Real.sin (2 * α)) • gammaR 0 + Real.cos (2 * α) • (gammaR 0 * gamma0123R) := by
                rw [Matrix.mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm, Matrix.mul_one]
    rw [hmat, dotProduct_smul_add, neg_mul]
  have hnorm : omega1 (chiralGaugeMat α *ᵥ Φ) ^ 2 + omega2 (chiralGaugeMat α *ᵥ Φ) ^ 2 =
      omega1 Φ ^ 2 + omega2 Φ ^ 2 := by
    rw [h1, h2]
    linear_combination (omega1 Φ ^ 2 + omega2 Φ ^ 2) * Real.cos_sq_add_sin_sq (2 * α)
  have hJ : ∀ μ : Fin 4, electricCurrentJ (chiralGaugeMat α *ᵥ Φ) μ = electricCurrentJ Φ μ := by
    intro μ
    have hanti : gamma0123R * gammaR μ = -(gammaR μ * gamma0123R) :=
      eq_neg_of_add_eq_zero_left (gamma0123R_anticomm_gammaR μ)
    rw [electricCurrentJ_eq_dot_gamma0, electricCurrentJ_eq_dot_gamma0, dot_gamma0_mulVec,
      chiralGaugeMat_transpose_gamma0]
    have hmat :
        gammaR 0 * chiralGaugeMat α * (gammaR μ * chiralGaugeMat α) = gammaR 0 * gammaR μ := by
      calc
        gammaR 0 * chiralGaugeMat α * (gammaR μ * chiralGaugeMat α)
            = gammaR 0 * (chiralGaugeMat α * gammaR μ * chiralGaugeMat α) := by
                simp only [Matrix.mul_assoc]
        _ = gammaR 0 * gammaR μ := by
                rw [chiralGaugeMat_conj_anticomm hanti α]
    rw [hmat]
  have hS : ∀ μ : Fin 4, axialCurrentSigma (chiralGaugeMat α *ᵥ Φ) μ = axialCurrentSigma Φ μ := by
    intro μ
    have hanti5 : gamma0123R * (gammaR μ * gamma5Real ⟨2, by decide⟩) =
        -((gammaR μ * gamma5Real ⟨2, by decide⟩) * gamma0123R) := by
      have hg : gamma0123R * gammaR μ = -(gammaR μ * gamma0123R) :=
        eq_neg_of_add_eq_zero_left (gamma0123R_anticomm_gammaR μ)
      have hp : gamma0123R * quatPR 2 = quatPR 2 * gamma0123R := gamma0123R_comm_quatPR 2
      dsimp [gamma5Real]
      calc
        gamma0123R * (gammaR μ * (gamma0123R * quatPR 2))
            = (gamma0123R * gammaR μ) * (gamma0123R * quatPR 2) := by rw [← Matrix.mul_assoc]
        _ = -(gammaR μ * gamma0123R) * (gamma0123R * quatPR 2) := by rw [hg]
        _ = -(gammaR μ * (gamma0123R * (gamma0123R * quatPR 2))) := by
              rw [neg_mul, Matrix.mul_assoc]
        _ = -(gammaR μ * (gamma0123R * (quatPR 2 * gamma0123R))) := by rw [hp]
        _ = -((gammaR μ * (gamma0123R * quatPR 2)) * gamma0123R) := by
              simp only [Matrix.mul_assoc]
    rw [axialCurrentSigma_eq_dot_gamma0, axialCurrentSigma_eq_dot_gamma0, dot_gamma0_mulVec,
      chiralGaugeMat_transpose_gamma0]
    have hmat :
        gammaR 0 * chiralGaugeMat α * ((gammaR μ * gamma5Real ⟨2, by decide⟩) * chiralGaugeMat α) =
          gammaR 0 * (gammaR μ * gamma5Real ⟨2, by decide⟩) := by
      calc
        gammaR 0 * chiralGaugeMat α * ((gammaR μ * gamma5Real ⟨2, by decide⟩) * chiralGaugeMat α)
            = gammaR 0 *
                (chiralGaugeMat α * (gammaR μ * gamma5Real ⟨2, by decide⟩) * chiralGaugeMat α) := by
                simp only [Matrix.mul_assoc]
        _ = gammaR 0 * (gammaR μ * gamma5Real ⟨2, by decide⟩) := by
                rw [chiralGaugeMat_conj_anticomm hanti5 α]
    rw [hmat]
  exact ⟨h1, h2, hnorm, hJ, hS⟩

private def electricGaugeConjMat (α : ℝ) : Mat8R :=
  Real.cos α • (1 : Mat8R) - Real.sin α • quatPR 2

private lemma electricGaugeMat_transpose_gamma0 (α : ℝ) :
    (electricGaugeMat α)ᵀ * gammaR 0 = gammaR 0 * electricGaugeConjMat α := by
  dsimp [electricGaugeMat, electricGaugeConjMat]
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    quatPR_transpose 2, Matrix.add_mul, Matrix.mul_sub, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, Matrix.one_mul, Matrix.mul_one, smul_neg, neg_mul,
    Algebra.smul_mul_assoc, ← gammaR_comm_quatPR 0 2, ← Algebra.mul_smul_comm, sub_eq_add_neg]

private lemma electricGauge_sandwich {X : Mat8R} (hX : X * quatPR 2 = quatPR 2 * X) (α : ℝ) :
    (electricGaugeMat α)ᵀ * gammaR 0 * (X * electricGaugeMat α) = gammaR 0 * X := by
  have hcommConj : electricGaugeConjMat α * X = X * electricGaugeConjMat α := by
    dsimp [electricGaugeConjMat]
    rw [Matrix.sub_mul, Matrix.mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hX]
  have hpair : electricGaugeConjMat α * electricGaugeMat α = (1 : Mat8R) := by
    dsimp [electricGaugeConjMat, electricGaugeMat]
    rw [sub_eq_add_neg, ← neg_smul, trig_sq_unit_prod (quatPR 2) (quatPR_sq 2)]
    have hcs : Real.cos α * Real.cos α - (-Real.sin α) * Real.sin α = 1 := by
      simpa [sq, sub_eq_add_neg] using Real.cos_sq_add_sin_sq α
    have h0 : Real.cos α * Real.sin α + (-Real.sin α) * Real.cos α = 0 := by ring
    rw [hcs, h0, zero_smul, one_smul, add_zero]
  calc
    (electricGaugeMat α)ᵀ * gammaR 0 * (X * electricGaugeMat α)
        = gammaR 0 * electricGaugeConjMat α * (X * electricGaugeMat α) := by
            rw [electricGaugeMat_transpose_gamma0]
    _ = gammaR 0 * ((electricGaugeConjMat α * X) * electricGaugeMat α) := by
            simp only [Matrix.mul_assoc]
    _ = gammaR 0 * (X * (electricGaugeConjMat α * electricGaugeMat α)) := by
            rw [hcommConj, Matrix.mul_assoc]
    _ = gammaR 0 * X := by
            rw [hpair, Matrix.mul_one]

/-- **Daviau Electric Gauge Invariance Theorem (Daviau Eq. 14 / Weyl Gauge)**:
unlike Lochak's chiral gauge `exp(α Γ⁰¹²³)`, Daviau's electric gauge `exp(α P₃)` leaves ALL four
densities `Ω₁`, `Ω₂`, `J^μ`, and `Σ^μ` strictly invariant. -/
theorem daviau_electric_gauge_invariance (α : ℝ) (Φ : Vec8R) :
    omega1 (electricGaugeMat α *ᵥ Φ) = omega1 Φ ∧
    omega2 (electricGaugeMat α *ᵥ Φ) = omega2 Φ ∧
    (∀ μ : Fin 4, electricCurrentJ (electricGaugeMat α *ᵥ Φ) μ = electricCurrentJ Φ μ) ∧
    (∀ μ : Fin 4, axialCurrentSigma (electricGaugeMat α *ᵥ Φ) μ = axialCurrentSigma Φ μ) := by
  have h1 : omega1 (electricGaugeMat α *ᵥ Φ) = omega1 Φ := by
    rw [omega1_eq_dot_gamma0, omega1_eq_dot_gamma0, dot_gamma0_id_mulVec]
    have hs := electricGauge_sandwich (X := (1 : Mat8R)) (by simp) α
    rw [Matrix.one_mul] at hs
    rw [hs, Matrix.mul_one]
  have h2 : omega2 (electricGaugeMat α *ᵥ Φ) = omega2 Φ := by
    rw [omega2_eq_dot_gamma0, omega2_eq_dot_gamma0, dot_gamma0_mulVec,
      electricGauge_sandwich (gamma0123R_comm_quatPR 2) α]
  have hJ : ∀ μ : Fin 4, electricCurrentJ (electricGaugeMat α *ᵥ Φ) μ = electricCurrentJ Φ μ := by
    intro μ
    rw [electricCurrentJ_eq_dot_gamma0, electricCurrentJ_eq_dot_gamma0, dot_gamma0_mulVec,
      electricGauge_sandwich (gammaR_comm_quatPR μ 2) α]
  have hS : ∀ μ : Fin 4, axialCurrentSigma (electricGaugeMat α *ᵥ Φ) μ = axialCurrentSigma Φ μ := by
    intro μ
    have hcomm5 :
        (gammaR μ * gamma5Real ⟨2, by decide⟩) * quatPR 2 =
          quatPR 2 * (gammaR μ * gamma5Real ⟨2, by decide⟩) := by
      dsimp [gamma5Real]
      calc
        (gammaR μ * (gamma0123R * quatPR 2)) * quatPR 2
            = gammaR μ * ((gamma0123R * quatPR 2) * quatPR 2) := by
                rw [Matrix.mul_assoc]
        _ = gammaR μ * ((quatPR 2 * gamma0123R) * quatPR 2) := by
                rw [gamma0123R_comm_quatPR 2]
        _ = (gammaR μ * quatPR 2) * (gamma0123R * quatPR 2) := by
                simp only [Matrix.mul_assoc]
        _ = (quatPR 2 * gammaR μ) * (gamma0123R * quatPR 2) := by
                rw [gammaR_comm_quatPR μ 2]
        _ = quatPR 2 * (gammaR μ * (gamma0123R * quatPR 2)) := by
                simp only [Matrix.mul_assoc]
    rw [axialCurrentSigma_eq_dot_gamma0, axialCurrentSigma_eq_dot_gamma0, dot_gamma0_mulVec,
      electricGauge_sandwich hcomm5 α]
  exact ⟨h1, h2, hJ, hS⟩

/-! ### Part C: Matrix Derivation `mat8RingDeriv`, `logSoldering`, & Smooth `C^∞` Realization -/

/-- Entrywise lifting of any commutative-ring derivation `d : RingDeriv R` to `M₈(R)`. -/
def mat8RingDeriv {R : Type*} [CommRing R] (d : RingDeriv R) :
    RingDeriv (Matrix (Fin 8) (Fin 8) R) where
  toFun A i j := d (A i j)
  map_add' A B := by
    ext i j
    exact d.map_add (A i j) (B i j)
  map_mul' A B := by
    ext i j
    change d (∑ k : Fin 8, A i k * B k j) =
      (∑ k : Fin 8, A i k * d (B k j)) + (∑ k : Fin 8, d (A i k) * B k j)
    rw [ringDeriv_sum d Finset.univ (fun k => A i k * B k j)]
    simp_rw [d.map_mul]
    rw [Finset.sum_add_distrib]

theorem mat8RingDeriv_smul {R : Type*} [CommRing R] (d : RingDeriv R) (c : R)
    (A : Matrix (Fin 8) (Fin 8) R) :
    mat8RingDeriv d (c • A) = c • mat8RingDeriv d A + d c • A := by
  ext i j
  simp only [mat8RingDeriv, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, d.map_mul]
  rfl

/-- Lift an integer `8 × 8` matrix into `M₈(R)` over any commutative ring `R`. -/
def castZ8Ring (R : Type*) [CommRing R] (M : Mat8Z) : Matrix (Fin 8) (Fin 8) R :=
  (Int.castRingHom R).mapMatrix M

@[simp]
theorem castZ8Ring_mul (R : Type*) [CommRing R] (A B : Mat8Z) :
    castZ8Ring R (A * B) = castZ8Ring R A * castZ8Ring R B :=
  (Int.castRingHom R).mapMatrix.map_mul A B

@[simp]
theorem castZ8Ring_one (R : Type*) [CommRing R] :
    castZ8Ring R (1 : Mat8Z) = (1 : Matrix (Fin 8) (Fin 8) R) :=
  (Int.castRingHom R).mapMatrix.map_one

@[simp]
theorem castZ8Ring_neg (R : Type*) [CommRing R] (A : Mat8Z) :
    castZ8Ring R (-A) = -castZ8Ring R A :=
  (Int.castRingHom R).mapMatrix.map_neg A

theorem mat8RingDeriv_castZ8Ring {R : Type*} [CommRing R] (d : RingDeriv R) (M : Mat8Z) :
    mat8RingDeriv d (castZ8Ring R M) = 0 := by
  ext i j
  exact ringDeriv_intCast d (M i j)

/-- Unitary trigonometric gauge loop `g = c • I₈ + s • J` in `M₈(Rˣ)` for any generator
`J² = -I₈` and `c² + s² = 1`. -/
def trigGaugeUnit {R : Type*} [CommRing R] (J : Matrix (Fin 8) (Fin 8) R)
    (hJ2 : J * J = -1) (c s : R) (hcs : c ^ 2 + s ^ 2 = 1) :
    (Matrix (Fin 8) (Fin 8) R)ˣ where
  val := c • (1 : Matrix (Fin 8) (Fin 8) R) + s • J
  inv := c • (1 : Matrix (Fin 8) (Fin 8) R) - s • J
  val_inv := by
    rw [sub_eq_add_neg, ← neg_smul, trig_sq_unit_prod J hJ2]
    have h1 : c * c - s * -s = 1 := by linear_combination hcs
    have h0 : c * -s + s * c = 0 := by ring
    rw [h1, h0, zero_smul, one_smul, add_zero]
  inv_val := by
    rw [sub_eq_add_neg, ← neg_smul, trig_sq_unit_prod J hJ2]
    have h1 : c * c - -s * s = 1 := by linear_combination hcs
    have h0 : c * s + -s * c = 0 := by ring
    rw [h1, h0, zero_smul, one_smul, add_zero]

/-- **Generic Trigonometric Soldering Theorem**:
whenever `mat8RingDeriv d J = 0` and `(c, s)` satisfy `d c = -(θ' * s)`, `d s = θ' * c` with
`c² + s² = 1`, the Axiom 4 logarithmic soldering connection equals `θ' • J`:
`logSoldering (mat8RingDeriv d) (trigGaugeUnit J hJ2 c s hcs) = θ' • J`. -/
theorem trigGaugeUnit_logSoldering {R : Type*} [CommRing R] (d : RingDeriv R)
    (J : Matrix (Fin 8) (Fin 8) R) (hJ2 : J * J = -1) (c s θ' : R)
    (hcs : c ^ 2 + s ^ 2 = 1) (hJd : mat8RingDeriv d J = 0)
    (hdc : d c = -(θ' * s)) (hds : d s = θ' * c) :
    logSoldering (mat8RingDeriv d) (trigGaugeUnit J hJ2 c s hcs) = θ' • J := by
  dsimp [logSoldering, trigGaugeUnit]
  have h1 : mat8RingDeriv d (1 : Matrix (Fin 8) (Fin 8) R) = 0 :=
    (mat8RingDeriv d).map_one
  have hd :
      mat8RingDeriv d (c • (1 : Matrix (Fin 8) (Fin 8) R) + s • J) =
        (-(θ' * s)) • (1 : Matrix (Fin 8) (Fin 8) R) + (θ' * c) • J := by
    rw [(mat8RingDeriv d).map_add, mat8RingDeriv_smul, mat8RingDeriv_smul, h1, hJd,
      smul_zero, smul_zero, zero_add, zero_add, hdc, hds]
  rw [hd, sub_eq_add_neg, ← neg_smul, trig_sq_unit_prod J hJ2]
  have hscalar : c * -(θ' * s) - -s * (θ' * c) = 0 := by ring
  have hgen : c * (θ' * c) + -s * -(θ' * s) = θ' := by
    calc
      c * (θ' * c) + -s * -(θ' * s) = θ' * (c ^ 2 + s ^ 2) := by ring
      _ = θ' * 1 := by rw [hcs]
      _ = θ' := mul_one θ'
  rw [hscalar, hgen, zero_smul, zero_add]

section SmoothRealRing

open scoped ContDiff

/-- Concrete smooth real function ring `C^∞(ℝ, ℝ)` carrying an honest calculus derivation
`d/dt`. -/
@[ext]
structure SmoothRealFun where
  val : ℝ → ℝ
  contDiff : ContDiff ℝ ∞ val

instance : Inhabited SmoothRealFun :=
  ⟨⟨fun _ => 0, contDiff_const⟩⟩

private def sZero : SmoothRealFun := ⟨fun _ => 0, contDiff_const⟩
private def sOne : SmoothRealFun := ⟨fun _ => 1, contDiff_const⟩
private def sAdd (f g : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => f.val t + g.val t, f.contDiff.add g.contDiff⟩
private def sNeg (f : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => -f.val t, f.contDiff.neg⟩
private def sSub (f g : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => f.val t - g.val t, f.contDiff.sub g.contDiff⟩
private def sMul (f g : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => f.val t * g.val t, f.contDiff.mul g.contDiff⟩
private def sNsmul (n : ℕ) (f : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => (n : ℝ) * f.val t, contDiff_const.mul f.contDiff⟩
private def sZsmul (z : ℤ) (f : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => (z : ℝ) * f.val t, contDiff_const.mul f.contDiff⟩
private def sNpow (n : ℕ) (f : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => f.val t ^ n, f.contDiff.pow n⟩
private def sNatCast (n : ℕ) : SmoothRealFun :=
  ⟨fun _ => (n : ℝ), contDiff_const⟩
private def sIntCast (z : ℤ) : SmoothRealFun :=
  ⟨fun _ => (z : ℝ), contDiff_const⟩

instance : CommRing SmoothRealFun where
  zero := sZero
  one := sOne
  add := sAdd
  neg := sNeg
  sub := sSub
  mul := sMul
  nsmul := sNsmul
  zsmul := sZsmul
  npow := sNpow
  natCast := sNatCast
  intCast := sIntCast
  add_assoc a b c := by ext t; change (a.val t + b.val t) + c.val t = a.val t + (b.val t + c.val t); ring
  zero_add a := by ext t; change 0 + a.val t = a.val t; ring
  add_zero a := by ext t; change a.val t + 0 = a.val t; ring
  nsmul_zero a := by ext t; change ((0 : ℕ) : ℝ) * a.val t = 0; simp
  nsmul_succ n a := by ext t; change ((n + 1 : ℕ) : ℝ) * a.val t = (n : ℝ) * a.val t + a.val t; push_cast; ring
  neg_add_cancel a := by ext t; change -a.val t + a.val t = 0; ring
  add_comm a b := by ext t; change a.val t + b.val t = b.val t + a.val t; ring
  sub_eq_add_neg a b := by ext t; change a.val t - b.val t = a.val t + -b.val t; ring
  zsmul_zero' a := by ext t; change ((0 : ℤ) : ℝ) * a.val t = 0; simp
  zsmul_succ' n a := by ext t; change ((↑(n.succ) : ℤ) : ℝ) * a.val t = ((n : ℤ) : ℝ) * a.val t + a.val t; push_cast; ring
  zsmul_neg' n a := by ext t; change ((Int.negSucc n : ℤ) : ℝ) * a.val t = -(((n.succ : ℤ) : ℝ) * a.val t); push_cast; ring
  left_distrib a b c := by ext t; change a.val t * (b.val t + c.val t) = a.val t * b.val t + a.val t * c.val t; ring
  right_distrib a b c := by ext t; change (a.val t + b.val t) * c.val t = a.val t * c.val t + b.val t * c.val t; ring
  zero_mul a := by ext t; change 0 * a.val t = 0; ring
  mul_zero a := by ext t; change a.val t * 0 = 0; ring
  mul_assoc a b c := by ext t; change (a.val t * b.val t) * c.val t = a.val t * (b.val t * c.val t); ring
  one_mul a := by ext t; change 1 * a.val t = a.val t; ring
  mul_one a := by ext t; change a.val t * 1 = a.val t; ring
  natCast_zero := by ext t; change ((0 : ℕ) : ℝ) = 0; simp
  natCast_succ n := by ext t; change ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1; push_cast; ring
  intCast_ofNat n := by ext t; change ((n : ℤ) : ℝ) = (n : ℝ); simp
  intCast_negSucc n := by ext t; change ((Int.negSucc n : ℤ) : ℝ) = -(((n + 1 : ℕ) : ℝ)); push_cast; ring
  npow_zero a := by ext t; change a.val t ^ 0 = 1; simp
  npow_succ n a := by ext t; change a.val t ^ (n + 1) = a.val t ^ n * a.val t; ring
  mul_comm a b := by ext t; change a.val t * b.val t = b.val t * a.val t; ring

/-- Ordinary real derivative `f ↦ f'` as an exact `RingDeriv SmoothRealFun`. -/
def smoothDeriv : RingDeriv SmoothRealFun where
  toFun f := ⟨deriv f.val, (contDiff_infty_iff_deriv.mp f.contDiff).2⟩
  map_add' f g := by
    ext t
    have hf : DifferentiableAt ℝ f.val t := (contDiff_infty_iff_deriv.mp f.contDiff).1 t
    have hg : DifferentiableAt ℝ g.val t := (contDiff_infty_iff_deriv.mp g.contDiff).1 t
    exact deriv_add hf hg
  map_mul' f g := by
    ext t
    have hf : DifferentiableAt ℝ f.val t := (contDiff_infty_iff_deriv.mp f.contDiff).1 t
    have hg : DifferentiableAt ℝ g.val t := (contDiff_infty_iff_deriv.mp g.contDiff).1 t
    change deriv (fun x => f.val x * g.val x) t =
      f.val t * deriv g.val t + deriv f.val t * g.val t
    exact (hf.hasDerivAt.mul hg.hasDerivAt).deriv.trans (by ring)

def smoothCos (θ : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => Real.cos (θ.val t), Real.contDiff_cos.comp θ.contDiff⟩

def smoothSin (θ : SmoothRealFun) : SmoothRealFun :=
  ⟨fun t => Real.sin (θ.val t), Real.contDiff_sin.comp θ.contDiff⟩

theorem smoothCos_sq_add_sin_sq (θ : SmoothRealFun) :
    smoothCos θ ^ 2 + smoothSin θ ^ 2 = 1 := by
  ext t
  change Real.cos (θ.val t) ^ 2 + Real.sin (θ.val t) ^ 2 = 1
  exact Real.cos_sq_add_sin_sq (θ.val t)

theorem smoothDeriv_cos (θ : SmoothRealFun) :
    smoothDeriv (smoothCos θ) = -(smoothDeriv θ * smoothSin θ) := by
  ext t
  have hθ : HasDerivAt θ.val (deriv θ.val t) t :=
    ((contDiff_infty_iff_deriv.mp θ.contDiff).1 t).hasDerivAt
  have hc : HasDerivAt (fun x => Real.cos (θ.val x)) (-Real.sin (θ.val t) * deriv θ.val t) t :=
    (Real.hasDerivAt_cos (θ.val t)).comp t hθ
  change deriv (fun x => Real.cos (θ.val x)) t = -(deriv θ.val t * Real.sin (θ.val t))
  rw [hc.deriv]
  ring

theorem smoothDeriv_sin (θ : SmoothRealFun) :
    smoothDeriv (smoothSin θ) = smoothDeriv θ * smoothCos θ := by
  ext t
  have hθ : HasDerivAt θ.val (deriv θ.val t) t :=
    ((contDiff_infty_iff_deriv.mp θ.contDiff).1 t).hasDerivAt
  have hs : HasDerivAt (fun x => Real.sin (θ.val x)) (Real.cos (θ.val t) * deriv θ.val t) t :=
    (Real.hasDerivAt_sin (θ.val t)).comp t hθ
  change deriv (fun x => Real.sin (θ.val x)) t = deriv θ.val t * Real.cos (θ.val t)
  rw [hs.deriv]
  ring

private lemma gamma0123Smooth_sq :
    castZ8Ring SmoothRealFun gamma0123Z * castZ8Ring SmoothRealFun gamma0123Z = -1 := by
  rw [← castZ8Ring_mul, gamma0123Z_sq, castZ8Ring_neg, castZ8Ring_one]

private lemma p3Z_sq_int : p3Z * p3Z = -(1 : Mat8Z) := by
  decide

private lemma p3Smooth_sq :
    castZ8Ring SmoothRealFun p3Z * castZ8Ring SmoothRealFun p3Z = -1 := by
  rw [← castZ8Ring_mul, p3Z_sq_int, castZ8Ring_neg, castZ8Ring_one]

/-- Smooth chiral gauge unit `U(θ) = cos(θ) I₈ + sin(θ) Γ⁰¹²³` over `M₈(C^∞(ℝ, ℝ))ˣ`. -/
def smoothChiralGaugeUnit (θ : SmoothRealFun) : (Matrix (Fin 8) (Fin 8) SmoothRealFun)ˣ :=
  trigGaugeUnit (castZ8Ring SmoothRealFun gamma0123Z) gamma0123Smooth_sq
    (smoothCos θ) (smoothSin θ) (smoothCos_sq_add_sin_sq θ)

/-- Smooth electric gauge unit `E(θ) = cos(θ) I₈ + sin(θ) P₃` over `M₈(C^∞(ℝ, ℝ))ˣ`. -/
def smoothElectricGaugeUnit (θ : SmoothRealFun) : (Matrix (Fin 8) (Fin 8) SmoothRealFun)ˣ :=
  trigGaugeUnit (castZ8Ring SmoothRealFun p3Z) p3Smooth_sq
    (smoothCos θ) (smoothSin θ) (smoothCos_sq_add_sin_sq θ)

/-- Exact calculus soldering identity for smooth chiral gauge curves
`U(θ(t)) = cos(θ(t)) I₈ + sin(θ(t)) Γ⁰¹²³`:
`logSoldering (mat8RingDeriv smoothDeriv) U(θ) = θ' • Γ⁰¹²³`. -/
theorem smoothChiralGaugeUnit_logSoldering (θ : SmoothRealFun) :
    logSoldering (mat8RingDeriv smoothDeriv) (smoothChiralGaugeUnit θ) =
      smoothDeriv θ • castZ8Ring SmoothRealFun gamma0123Z :=
  trigGaugeUnit_logSoldering smoothDeriv (castZ8Ring SmoothRealFun gamma0123Z) gamma0123Smooth_sq
    (smoothCos θ) (smoothSin θ) (smoothDeriv θ) (smoothCos_sq_add_sin_sq θ)
    (mat8RingDeriv_castZ8Ring smoothDeriv gamma0123Z) (smoothDeriv_cos θ) (smoothDeriv_sin θ)

/-- Exact calculus soldering identity for smooth electric gauge curves
`E(θ(t)) = cos(θ(t)) I₈ + sin(θ(t)) P₃`:
`logSoldering (mat8RingDeriv smoothDeriv) E(θ) = θ' • P₃`. -/
theorem smoothElectricGaugeUnit_logSoldering (θ : SmoothRealFun) :
    logSoldering (mat8RingDeriv smoothDeriv) (smoothElectricGaugeUnit θ) =
      smoothDeriv θ • castZ8Ring SmoothRealFun p3Z :=
  trigGaugeUnit_logSoldering smoothDeriv (castZ8Ring SmoothRealFun p3Z) p3Smooth_sq
    (smoothCos θ) (smoothSin θ) (smoothDeriv θ) (smoothCos_sq_add_sin_sq θ)
    (mat8RingDeriv_castZ8Ring smoothDeriv p3Z) (smoothDeriv_cos θ) (smoothDeriv_sin θ)

/-- Linear angle function `θ(t) = vel * t` in `SmoothRealFun`, giving nonzero constant velocity
`smoothDeriv (linearAngle vel) = vel • 1`. -/
def linearAngle (vel : ℝ) : SmoothRealFun :=
  ⟨fun t => vel * t, contDiff_const.mul contDiff_id⟩

theorem linearAngle_soldering_velocity (vel : ℝ) (t : ℝ) :
    (smoothDeriv (linearAngle vel)).val t = vel := by
  have h : HasDerivAt (fun x : ℝ => vel * x) (vel * 1) t :=
    (hasDerivAt_id' t).const_mul vel
  change deriv (fun x : ℝ => vel * x) t = vel
  rw [h.deriv, mul_one]

end SmoothRealRing

/-! ### Part D: Matching Chiral Soldering Connection onto Rodichev Axial Torsion -/

/-- **Chiral Soldering–Rodichev Torsion Equivalence**:
weighting the covector chiral soldering connection `ω_ν = (-½ σ_ν) Γ⁰¹²³` by `Γ_ν` on the left
and `P_{j+1}` on the right reproduces Rodichev's skew-torsion Dirac coupling
(`rodichev_chiral_torsion_dirac_term`):
`∑_ν Γ_ν ((-½ σ_ν) Γ⁰¹²³) P_{j+1} = (∑_{a,μ,b} Φ_{[aμb]} Γ^μ Γ^a Γ^b) (-1/12 P_{j+1})`. -/
theorem chiral_soldering_matches_rodichev_torsion (σ : Fin 4 → ℝ) (j : Fin 3) :
    ∑ ν : Fin 4, gammaLowR ν * ((-(1 / 2 : ℝ) * σ ν) • gamma0123R) * quatPR j =
      (∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        rodichevTorsion σ a μ b • (gammaR μ * gammaR a * gammaR b)) *
          (-(1 / 12 : ℝ) • quatPR j) := by
  rw [rodichev_chiral_torsion_dirac_term σ j, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  dsimp [gamma5Real]
  rw [Matrix.mul_assoc]

end InfoGeometry.Clifford.DaviauLochakDifferentialGauge
