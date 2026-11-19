/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParaKahlerBregmanModularNoetherPoset
import InfoGeometry.Physics.CubicNLSAKNSLaxPair
import InfoGeometry.Canonical.ManakovZornSolitonLaxBridge
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
import InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
import InfoGeometry.Twistor.WeylZornMajoranaNambu
import InfoGeometry.Algebra.CircularChiralOperatorEightBridge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Archetypes `MA₆` & `MA₇`: Chiral `N₊/N₋` Spinor Fluid, Spectral Noncommutative AKNS–Lax Pair, Split-Octonion Birefringence, & Dynamical Vacuum Mass

Formalizes the chiral-fluid, integrable Lax, and dynamical-mass core requested alongside
the second part of Philip Mannheim's lecture:

1. **Archetype `MA₆` — Chiral `N₊/N₋` Spinor Fluid, Majorana/Weyl Circular Basis, Noncommutative Spectral AKNS–Lax Pair & Split-Octonion Birefringence**:
   - Bridges the real Majorana / Weyl chirality split (`WeylZornMajoranaNambu`), the 8-element
     circular split-octonion Peirce frame (`CircularChiralOperatorEightBridge`), and the Peirce
     spine circular light-cone Faraday gyrotropy & Zakharov–Shabat Lax pair (`ParaKahlerBregmanModularNoetherPoset`);
   - **Noncommutative Spectral-Parameter AKNS–Lax Zero-Curvature Theorem (`[CommRing R] [Ring B] [Algebra R B]`)**:
     for any idempotent `P * P = P` and spectral parameter `ζ : R`, the spectral Lax pair
     `U(ζ) = ζ • invS P + genPhi P A C` and
     `W(ζ) = (2 * ζ ^ 2) • invS P + (2 * ζ) • genPhi P A C + (genJ P Ax Cx - genSig P A C)`
     has all `ζ³`, `ζ²`, and `ζ` curvature terms cancel identically, collapsing `U_t - W_x + [U, W]`
     onto `(At_corner - Axx_corner + 2 • N₊ N₋ N₊) + (Ct_corner + Cxx_corner - 2 • N₋ N₊ N₋)`,
     which vanishes **if and only if** both coupled noncommutative cubic NLS equations hold;
   - **Exact Complex `M₂(ℂ)` AKNS Equivalence**: maps `(U, I • W)` under `ζ = -I * spectral`
     and Wick time `At = upperMat2 (-i q_t)`, `Ct = lowerMat2 (-i r_t)` directly to
     `CubicNLSAKNSLaxPair.spatial`, `CubicNLSAKNSLaxPair.temporal`, and `CubicNLSAKNSLaxPair.curvature`;
   - **Dirac–Zorn Birefringence & Manakov XPM**: decomposes the cubic off-diagonal self-interaction
     of `diracZornOp 0 0 u v` into isotropic Kerr `zornDot` + chiral `vecOp (zornCross u v)`.

2. **Archetype `MA₇` — Spontaneous Symmetry Breaking, NJL `Λ²` Gap Cancellation & Dynamical Double-Well Mass**:
   - Goldstone flat rim (`HasDerivAt = 0` along `v (cos θ, sin θ)`) vs. massive radial Higgs shift
     (`μ² h² + λ v h³ + (λ/4) h⁴`);
   - Exact Hartree–Fock square completion `(g / 2) (c - m / g)² - m² / (2 g)` and bare `Λ⁴, Λ²`
     counterterm subtraction;
   - Exact global minimum theorem for Mannheim's scale-free dynamical double-well potential
     `dynamicalDoubleWell M m = m⁴ log(m² / M²) - m⁴ / 2` (`≥ -M⁴ / 2` for all `m ≠ 0`, equality iff
     `m = ±M`, positive radial Higgs curvature `deriv (deriv _) M = 8 * M² > 0` via
     `Real.log_le_sub_one_of_pos`);
   - UV finiteness for `γ_θ = -1` (`1 - 1 / (1 + Λ) < 1`) and operator chiral condensate `Φ² = V`
     propagating through `NoncommutativeKreinMathlibBridge.ClTowerColimit`.
-/

noncomputable section

namespace InfoGeometry.Algebra.ChiralFluidNLSLaxAndDynamicalVacuumMass

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.ManakovZornSolitonLax
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Twistor.WeylZornMajoranaNambu
open InfoGeometry.Algebra.CircularChiralOperatorEightBridge
open InfoGeometry.Krein
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid
open InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
open InfoGeometry.Twistor.WeylZornMajoranaOperatorAction
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge (canonicalVectorEquiv)
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.MetaCompiler

/-! ## OpenGauss `T16`: Non-commutativity witness on `M₂(ℂ)` -/

/-- Closed `M₂(ℂ)` matrix non-commutativity witness for chiral Lax operators. -/
theorem chiral_lax_matrix2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℂ), 1; 0, 0], !![(0 : ℂ), 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h00
  norm_num at h00

/-! ## Archetype `MA₆`: Chiral `N₊/N₋` Spinor Fluid & Noncommutative AKNS–Lax Pair -/

section MA6_ChiralFluidNLSLax

/-- Noncommutative spectral-parameter AKNS spatial operator `U(ζ) = ζ • S_P + Φ(A, C)`. -/
def chiralLaxU {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (P A C : B) (ζ : R) : B :=
  ζ • invS P + genPhi P A C

/-- Noncommutative spectral-parameter AKNS temporal operator
`W(ζ) = (2 ζ²) • S_P + (2 ζ) • Φ(A, C) + (J(Ax, Cx) - Σ(A, C))`. -/
def chiralLaxW {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P A C Ax Cx : B) (ζ : R) : B :=
  ((2 : R) * ζ ^ 2) • invS P + ((2 : R) * ζ) • genPhi P A C + (genJ P Ax Cx - genSig P A C)

/-- Spatial x-derivative jet `W_x` of `chiralLaxW`. -/
def chiralLaxWx {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P A C Ax Cx Axx Cxx : B) (ζ : R) : B :=
  ((2 : R) * ζ) • genPhi P Ax Cx +
    (genJ P Axx Cxx - (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P Ax) (coneMinus P C) +
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P Cx)))

/-- Noncommutative Wick AKNS zero-curvature residual `U_t - W_x + [U, W]`. -/
def chiralLaxCurvature {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (P A C Ax Cx Axx Cxx At Ct : B) (ζ : R) : B :=
  genPhi P At Ct - chiralLaxWx P A C Ax Cx Axx Cxx ζ +
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (chiralLaxU P A C ζ) (chiralLaxW P A C Ax Cx ζ)

/-- Upper-sheet coupled noncommutative cubic NLS residual on `N₊`. -/
def nlsPlusResidual {B : Type*} [Ring B] (P A C Axx At : B) : B :=
  conePlus P At - conePlus P Axx + (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A)

/-- Lower-sheet coupled noncommutative cubic NLS residual on `N₋`. -/
def nlsMinusResidual {B : Type*} [Ring B] (P A C Cxx Ct : B) : B :=
  coneMinus P Ct + coneMinus P Cxx - (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)

/-- `2 × 2` idempotent projector `diag(1, 0)` in `M₂(ℂ)`. -/
def projMat2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Off-diagonal upper channel matrix `[[0, x], [0, 0]]` in `M₂(ℂ)`. -/
def upperMat2 (x : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, x; 0, 0]

/-- Off-diagonal lower channel matrix `[[0, 0], [y, 0]]` in `M₂(ℂ)`. -/
def lowerMat2 (y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; y, 0]

lemma comm_self_eq_zero {B : Type*} [Ring B] (X : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm X X = 0 :=
  sub_self (X * X)

lemma comm_add_left' {B : Type*} [Ring B] (X Y Z : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (X + Y) Z =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Z +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm Y Z := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  noncomm_ring

lemma comm_add_right' {B : Type*} [Ring B] (X Y Z : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm X (Y + Z) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Y +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Z := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  noncomm_ring

lemma comm_smul_left' {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (r : R) (X Y : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (r • X) Y =
      r • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Y := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  rw [smul_sub, smul_mul_assoc, mul_smul_comm]

lemma comm_smul_right' {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (r : R) (X Y : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm X (r • Y) =
      r • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Y := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  rw [smul_sub, smul_mul_assoc, mul_smul_comm]

/-- **Chiral Spinor Majorana/Weyl Circular Split-Octonion Basis & Gyrotropy Bridge**:
Unites the repository's real Majorana/Weyl Zorn spinors (`WeylZornMajoranaNambu`), the 8-element
circular Peirce split-octonion operator frame (`CircularChiralOperatorEightBridge`), and the
Peirce spine circular light-cone Faraday gyrotropy and Zakharov–Shabat NLS commutator (`PeirceSpine`). -/
theorem chiral_fluid_majorana_weyl_circular_basis :
    (∀ i : Fin 3, zornModeGrading i * majorana i + majorana i * zornModeGrading i = 0 ∧
      (∀ x, majorana i (doubledZornEquiv i x) = doubledZornEquiv i (modular_j x)) ∧
      weylChirality (1 : InfoGeometry.Canonical.ZornMatrix ℝ) ≠ zornModeGrading i 1) ∧
    (Function.Injective operatorFrame ∧ Eplus ≠ Eminus ∧
      (∀ i : Fin 8, operatorFrame i = canonicalVectorEquiv (circularPeirceBasis i))) ∧
    (∀ {B : Type} [Ring B] {P : B}, P * P = P → ∀ (A C : B),
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (nlsLaxL P A C) (nlsLaxM P A C) =
        -((2 : ℤ) • ((genV P A C * genV P A C) * genJ P A C))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨zornModeGrading_anticommutes_majorana i,
      fun x => majorana_intertwines_nambu_swap i x,
      weylChirality_ne_modeGrading_on_one i⟩
  · refine ⟨operatorFrame_injective, ?_, operatorFrame_eq_circularPeirce⟩
    exact operatorFrame_ne_of_ne (i := 0) (j := 4) (by decide)
  · intro B _ P hP A C
    have hm4 := archetype_M4_circularly_polarized_lightcone_and_faraday_gyrotropy hP A C
    have hm5 := archetype_M5_four_wave_mixing_and_zakharov_shabat_nls_lax_pair hP A C
    exact ⟨hm4.1, hm4.2.1, hm4.2.2.1, hm4.2.2.2.1, hm5.2.2.2.2⟩

/-- **Noncommutative Spectral-Parameter Chiral AKNS–Lax Zero-Curvature Theorem (`[Algebra R B]`)**:
For any commutative scalar ring `R`, arbitrary associative ring `B` with `[Algebra R B]`,
idempotent `P * P = P`, and spectral parameter `ζ : R`, all spectral terms in `ζ³`, `ζ²`, and
`ζ¹` cancel identically, giving:
1. `chiralLaxCurvature P A C Ax Cx Axx Cxx At Ct ζ = nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct`;
2. `chiralLaxCurvature P A C Ax Cx Axx Cxx At Ct ζ = 0 ↔ (nlsPlusResidual P A C Axx At = 0 ∧ nlsMinusResidual P A C Cxx Ct = 0)`. -/
theorem noncommutative_chiral_akns_lax_and_coupled_nls
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B] {P : B} (hP : P * P = P)
    (ζ : R) (A C Ax Cx Axx Cxx At Ct : B) :
    chiralLaxCurvature P A C Ax Cx Axx Cxx At Ct ζ =
      nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct ∧
    (chiralLaxCurvature P A C Ax Cx Axx Cxx At Ct ζ = 0 ↔
      nlsPlusResidual P A C Axx At = 0 ∧ nlsMinusResidual P A C Cxx Ct = 0) := by
  have h1 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genPhi P A C) +
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (invS P) = 0 := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; abel
  have hζ1 : InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genJ P Ax Cx - genSig P A C) =
      (2 : ℤ) • genPhi P Ax Cx := by
    peirce_nf hP
  have h0 : genPhi P At Ct -
      (genJ P Axx Cxx - (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P Ax) (coneMinus P C) +
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P Cx))) +
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P Ax Cx - genSig P A C) =
      nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct := by
    simp only [nlsPlusResidual, nlsMinusResidual]
    peirce_nf hP
  have hcomm_expand : InfoGeometry.OperatorAlgebra.PeirceSpine.comm (chiralLaxU P A C ζ) (chiralLaxW P A C Ax Cx ζ) =
      ((2 : R) * ζ) • genPhi P Ax Cx + InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P Ax Cx - genSig P A C) := by
    unfold chiralLaxU chiralLaxW
    rw [comm_add_left', comm_add_right', comm_add_right', comm_add_right', comm_add_right']
    simp only [comm_smul_left', comm_smul_right', comm_self_eq_zero, smul_zero, zero_add, add_zero]
    have hq1 : ζ • InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genJ P Ax Cx - genSig P A C) =
        ((2 : R) * ζ) • genPhi P Ax Cx := by
      rw [hζ1, ← Int.cast_smul_eq_zsmul R (2 : ℤ), smul_smul]
      congr 1
      norm_cast
      ring
    rw [smul_smul, add_add_add_comm, show ((2 : R) * ζ) * ζ = (2 : R) * ζ ^ 2 by ring,
      ← smul_add, h1, smul_zero, zero_add, hq1]
  have hcurv : chiralLaxCurvature P A C Ax Cx Axx Cxx At Ct ζ =
      nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct := by
    unfold chiralLaxCurvature chiralLaxWx
    rw [hcomm_expand]
    calc
      genPhi P At Ct -
          (((2 : R) * ζ) • genPhi P Ax Cx +
            (genJ P Axx Cxx - (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P Ax) (coneMinus P C) +
              InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P Cx)))) +
          (((2 : R) * ζ) • genPhi P Ax Cx +
            InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P Ax Cx - genSig P A C))
          = genPhi P At Ct -
              (genJ P Axx Cxx - (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P Ax) (coneMinus P C) +
                InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P Cx))) +
              InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P Ax Cx - genSig P A C) := by abel
      _ = nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct := h0
  refine ⟨hcurv, ?_⟩
  rw [hcurv]
  constructor
  · intro hsum
    have hP_proj : P * (nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct) =
        nlsPlusResidual P A C Axx At := by
      simp only [nlsPlusResidual, nlsMinusResidual]
      peirce_nf hP
    have hplus : nlsPlusResidual P A C Axx At = 0 := by
      calc
        nlsPlusResidual P A C Axx At
            = P * (nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct) := hP_proj.symm
        _ = P * 0 := by rw [hsum]
        _ = 0 := mul_zero P
    have hminus : nlsMinusResidual P A C Cxx Ct = 0 := by
      rw [hplus, zero_add] at hsum
      exact hsum
    exact ⟨hplus, hminus⟩
  · rintro ⟨hp, hm⟩
    rw [hp, hm, add_zero]

lemma projMat2_invS : invS projMat2 = !![1, 0; 0, (-1 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invS, projMat2]

lemma conePlus_projMat2 (x : ℂ) : conePlus projMat2 (upperMat2 x) = upperMat2 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conePlus, projMat2, upperMat2, Matrix.mul_apply, Fin.sum_univ_two]

lemma coneMinus_projMat2 (y : ℂ) : coneMinus projMat2 (lowerMat2 y) = lowerMat2 y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneMinus, projMat2, lowerMat2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Complex `M₂(ℂ)` AKNS Equivalence Theorem**:
Evaluating the abstract noncommutative chiral Lax pair in `B = Matrix (Fin 2) (Fin 2) ℂ` at
`P = projMat2`, `ζ = -I * spectral`, and Wick time derivatives `At = upperMat2 (-i qt)`,
`Ct = lowerMat2 (-i rt)` reproduces `InfoGeometry.Physics.CubicNLSAKNSLaxPair` identically:
`U = spatial`, `I • W = temporal`, and `I • curvature = CubicNLSAKNSLaxPair.curvature`. -/
theorem chiral_akns_lax_matrix2_complex_correspondence
    (spectral q r qx rx qxx rxx qt rt : ℂ) :
    projMat2 * projMat2 = projMat2 ∧
    chiralLaxU projMat2 (upperMat2 q) (lowerMat2 r) (-Complex.I * spectral) =
      InfoGeometry.Physics.CubicNLSAKNSLaxPair.spatial spectral q r ∧
    Complex.I • chiralLaxW projMat2 (upperMat2 q) (lowerMat2 r) (upperMat2 qx) (lowerMat2 rx)
        (-Complex.I * spectral) =
      InfoGeometry.Physics.CubicNLSAKNSLaxPair.temporal spectral q r qx rx ∧
    Complex.I • chiralLaxCurvature projMat2 (upperMat2 q) (lowerMat2 r)
        (upperMat2 qx) (lowerMat2 rx) (upperMat2 qxx) (lowerMat2 rxx)
        (upperMat2 (-Complex.I * qt)) (lowerMat2 (-Complex.I * rt)) (-Complex.I * spectral) =
      InfoGeometry.Physics.CubicNLSAKNSLaxPair.curvature spectral q r qx rx qt rt qxx rxx := by
  have hP : projMat2 * projMat2 = projMat2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [projMat2, Matrix.mul_apply, Fin.sum_univ_two]
  have hmain := (noncommutative_chiral_akns_lax_and_coupled_nls hP (-Complex.I * spectral)
    (upperMat2 q) (lowerMat2 r) (upperMat2 qx) (lowerMat2 rx)
    (upperMat2 qxx) (lowerMat2 rxx) (upperMat2 (-Complex.I * qt)) (lowerMat2 (-Complex.I * rt))).1
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, Complex.I_sq]
    ring
  refine ⟨hP, ?_, ?_, ?_⟩
  · simp only [chiralLaxU, projMat2_invS, genPhi, conePlus_projMat2, coneMinus_projMat2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperMat2, lowerMat2, InfoGeometry.Physics.CubicNLSAKNSLaxPair.spatial]
  · simp only [chiralLaxW, projMat2_invS, genPhi, genJ, genSig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm, conePlus_projMat2, coneMinus_projMat2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperMat2, lowerMat2, InfoGeometry.Physics.CubicNLSAKNSLaxPair.temporal]
    all_goals
      { try ring_nf
        try rw [Complex.I_sq]
        try rw [hI3]
        try ring }
  · rw [hmain, InfoGeometry.Physics.CubicNLSAKNSLaxPair.curvature_eq_nls_residuals]
    simp only [nlsPlusResidual, nlsMinusResidual, conePlus_projMat2, coneMinus_projMat2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperMat2, lowerMat2]
    all_goals
      { try ring_nf
        try rw [Complex.I_sq]
        try rw [hI3]
        try ring }

/-- **Split-Octonionic Dirac–Zorn Birefringent Cubic & Manakov XPM Synthesis**:
Over any commutative ring `[CommRing R]`, the off-diagonal two-sheeted Dirac–Zorn fluid element
`Z = diracZornOp 0 0 u₁ u₂ u₃ v₁ v₂ v₃ : NestedMat R` has:
1. Diagonal second power `(Z * Z) 0 0 = fiberEmbed (zornDot u v) + vecOp (zornCross1 u v) (zornCross2 u v) (zornCross3 u v)`;
2. Cubic off-diagonal interaction `(Z * Z * Z) 0 1` splitting cleanly into scalar `zornDot` Kerr
   self-interaction plus rotated chiral `vecOp (zornCross)` spin-birefringence;
3. Complete agreement with `ManakovZornSolitonLax.manakov_zorn_soliton_relations R` (`χ⁽³⁾ = 4`
   isotropic Kerr sum). -/
theorem diracZorn_birefringent_cubic_and_manakov_xpm
    (R : Type*) [CommRing R] (u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    let Z := diracZornOp (0 : R) 0 u₁ u₂ u₃ v₁ v₂ v₃
    (Z * Z) 0 0 =
      fiberEmbed (zornDot u₁ u₂ u₃ v₁ v₂ v₃) +
        vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃) (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃) (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃) ∧
    (Z * Z * Z) 0 1 =
      (fiberEmbed (zornDot u₁ u₂ u₃ v₁ v₂ v₃) +
        vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃) (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃) (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃)) *
        vecOp u₁ u₂ u₃ ∧
    (Z * Z * Z) 1 0 =
      (fiberEmbed (zornDot v₁ v₂ v₃ u₁ u₂ u₃) +
        vecOp (zornCross1 v₁ v₂ v₃ u₁ u₂ u₃) (zornCross2 v₁ v₂ v₃ u₁ u₂ u₃) (zornCross3 v₁ v₂ v₃ u₁ u₂ u₃)) *
        vecOp v₁ v₂ v₃ ∧
    manakovKerrEnergy (1 : R) 1 = 4 := by
  intro Z
  have hprod : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : R,
      vecOp a₁ a₂ a₃ * vecOp b₁ b₂ b₃ =
        fiberEmbed (zornDot a₁ a₂ a₃ b₁ b₂ b₃) +
          vecOp (zornCross1 a₁ a₂ a₃ b₁ b₂ b₃) (zornCross2 a₁ a₂ a₃ b₁ b₂ b₃) (zornCross3 a₁ a₂ a₃ b₁ b₂ b₃) :=
    fun a₁ a₂ a₃ b₁ b₂ b₃ => (zorn_vector_product_dot_plus_cross a₁ a₂ a₃ b₁ b₂ b₃ (0 : R) 0 0).1
  have hZ0 : fiberEmbed (0 : R) = 0 := by apply ext_fin2 <;> simp [fiberEmbed]
  have hZZ00 : (Z * Z) 0 0 = vecOp u₁ u₂ u₃ * vecOp v₁ v₂ v₃ := by
    simp [Z, diracZornOp, mul2_00, hZ0]
  have hZZ11 : (Z * Z) 1 1 = vecOp v₁ v₂ v₃ * vecOp u₁ u₂ u₃ := by
    simp [Z, diracZornOp, mul2_11, hZ0]
  have hZZ01 : (Z * Z) 0 1 = 0 := by simp [Z, diracZornOp, mul2_01, hZ0]
  have hZZ10 : (Z * Z) 1 0 = 0 := by simp [Z, diracZornOp, mul2_10, hZ0]
  have hZ01 : Z 0 1 = vecOp u₁ u₂ u₃ := rfl
  have hZ10 : Z 1 0 = vecOp v₁ v₂ v₃ := rfl
  refine ⟨?_, ?_, ?_, (manakov_zorn_soliton_relations R).2.2.2.2.2.2.2.1⟩
  · rw [hZZ00]; exact hprod u₁ u₂ u₃ v₁ v₂ v₃
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hZZ00, hZZ01, MulZeroClass.zero_mul, add_zero,
      hprod u₁ u₂ u₃ v₁ v₂ v₃, hZ01]
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hZZ10, hZZ11, MulZeroClass.zero_mul, zero_add,
      hprod v₁ v₂ v₃ u₁ u₂ u₃, hZ10]

end MA6_ChiralFluidNLSLax

/-! ## Archetype `MA₇`: Goldstone–Higgs Shift, NJL `Λ²` Cancellation & Dynamical Double-Well Mass -/

section MA7_DynamicalVacuumMass

/-- Classical Mexican-hat double-well scalar potential `V(x, y) = -μ² (x² + y²)/2 + λ (x² + y²)²/4`. -/
def mexicanHat2D (μSq lam x y : ℝ) : ℝ :=
  -(μSq / 2) * (x ^ 2 + y ^ 2) + (lam / 4) * (x ^ 2 + y ^ 2) ^ 2

/-- Bare NJL fermion-bubble vacuum energy `-Λ⁴ - 2 m² Λ² + m⁴ log(Λ² / m²)`. -/
def njlBareEnergy (Λ m : ℝ) : ℝ :=
  -Λ ^ 4 - 2 * m ^ 2 * Λ ^ 2 + m ^ 4 * Real.log (Λ ^ 2 / m ^ 2)

/-- Mannheim scale-free dynamical double-well potential `m⁴ log(m² / M²) - m⁴ / 2`. -/
def dynamicalDoubleWell (M m : ℝ) : ℝ :=
  m ^ 4 * Real.log (m ^ 2 / M ^ 2) - m ^ 4 / 2

lemma dynamicalDoubleWell_deriv1 (M : ℝ) {m : ℝ} (hM : 0 < M) (hm : m ≠ 0) :
    HasDerivAt (dynamicalDoubleWell M) (4 * m ^ 3 * Real.log (m ^ 2 / M ^ 2)) m := by
  have hm2 : m ^ 2 / M ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hm) (pow_ne_zero 2 (ne_of_gt hM))
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 / M ^ 2) ((2 * m) / M ^ 2) m :=
    ((hasDerivAt_pow 2 m).div_const (M ^ 2)).congr_deriv (by norm_num)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 / M ^ 2))
      ((m ^ 2 / M ^ 2)⁻¹ * ((2 * m) / M ^ 2)) m :=
    ((Real.hasDerivAt_log hm2).comp m hinner).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hp4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * m ^ 3) m :=
    (hasDerivAt_pow 4 m).congr_deriv (by norm_num)
  have hprod : HasDerivAt (fun x : ℝ => x ^ 4 * Real.log (x ^ 2 / M ^ 2))
      (4 * m ^ 3 * Real.log (m ^ 2 / M ^ 2) +
        m ^ 4 * ((m ^ 2 / M ^ 2)⁻¹ * ((2 * m) / M ^ 2))) m :=
    hp4.mul hlog
  have hsub : HasDerivAt (fun x : ℝ => x ^ 4 / 2) ((4 * m ^ 3) / 2) m :=
    hp4.div_const 2
  have htot : HasDerivAt (dynamicalDoubleWell M)
      ((4 * m ^ 3 * Real.log (m ^ 2 / M ^ 2) +
        m ^ 4 * ((m ^ 2 / M ^ 2)⁻¹ * ((2 * m) / M ^ 2))) - (4 * m ^ 3) / 2) m :=
    (hprod.sub hsub).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  refine htot.congr_deriv ?_
  have hM0 : M ≠ 0 := ne_of_gt hM
  field_simp [hm, hM0]
  ring

/-- **Goldstone–Higgs Shift, NJL `Λ²` Cancellation & Scale-Free Dynamical Double-Well Theorem**:
1. **Mexican-Hat Nambu–Goldstone vs. Radial Higgs**: along the angular Goldstone manifold
   `θ ↦ (v cos θ, v sin θ)`, the potential is flat (`HasDerivAt = 0`), while shifting radially
   `x = v + h` at `λ v² = μ²` eliminates the linear term leaving `μ² h² + λ v h³ + (λ/4) h⁴`;
2. **Hartree–Fock & NJL Counterterm Cancellation**:
   `(g / 2) (c - m / g)² - m² / (2 g) = (g / 2) c² - m c` and
   `njlBareEnergy Λ m - njlBareEnergy Λ 0 + 2 m² Λ² = m⁴ log(Λ² / m²)` (free of `Λ⁴, Λ²`);
3. **Mannheim Dynamical Double-Well Global Minimum & Positive Higgs Mass**:
   For `0 < M` and `m ≠ 0`, `-(M⁴ / 2) ≤ dynamicalDoubleWell M m` with equality **iff** `m = M ∨ m = -M`
   (strictly below `dynamicalDoubleWell M 0 = 0`), with `deriv (dynamicalDoubleWell M) M = 0` and
   strictly positive Higgs curvature `deriv (deriv (dynamicalDoubleWell M)) M = 8 M² > 0`;
4. **UV Finiteness & All-Scales Noncommutative Chiral Condensate**:
   `γ_θ = -1` UV bound `0 < 1 - 1 / (1 + Λ) < 1` for `Λ > 0`, together with `genPhi P A C ^ 2 = genV P A C`
   and colimit propagation across `ClTowerColimit B`. -/
theorem dynamical_mass_goldstone_njl_and_vacuum_doublewell :
    (∀ μSq lam v θ : ℝ,
      HasDerivAt (fun α : ℝ => mexicanHat2D μSq lam (v * Real.cos α) (v * Real.sin α)) 0 θ) ∧
    (∀ μSq lam v h : ℝ, lam * v ^ 2 = μSq →
      mexicanHat2D μSq lam (v + h) 0 - mexicanHat2D μSq lam v 0 =
        μSq * h ^ 2 + lam * v * h ^ 3 + (lam / 4) * h ^ 4) ∧
    (∀ g c m : ℝ, g ≠ 0 → (g / 2) * (c - m / g) ^ 2 - m ^ 2 / (2 * g) = (g / 2) * c ^ 2 - m * c) ∧
    (∀ Λ m : ℝ, njlBareEnergy Λ m - njlBareEnergy Λ 0 + 2 * m ^ 2 * Λ ^ 2 =
      m ^ 4 * Real.log (Λ ^ 2 / m ^ 2)) ∧
    (∀ M m : ℝ, 0 < M → m ≠ 0 →
      -(M ^ 4 / 2) ≤ dynamicalDoubleWell M m ∧
      (dynamicalDoubleWell M m = -(M ^ 4 / 2) ↔ m = M ∨ m = -M) ∧
      -(M ^ 4 / 2) < dynamicalDoubleWell M 0) ∧
    (∀ M : ℝ, 0 < M →
      deriv (dynamicalDoubleWell M) M = 0 ∧
      deriv (deriv (dynamicalDoubleWell M)) M = 8 * M ^ 2 ∧
      0 < deriv (deriv (dynamicalDoubleWell M)) M) ∧
    (∀ Λ : ℝ, 0 < Λ → 0 < 1 - 1 / (1 + Λ) ∧ 1 - 1 / (1 + Λ) < 1) ∧
    (∀ {B : Type} [Ring B] {P : B}, P * P = P → ∀ (A C : B) (m n : ℕ) (hmn : m ≤ n)
      (X : ClTower B m),
      genPhi P A C * genPhi P A C = genV P A C ∧
      (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) n).hom (clTowerHom B hmn X) =
        (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μSq lam v θ
    have hev : (fun α : ℝ => mexicanHat2D μSq lam (v * Real.cos α) (v * Real.sin α)) =
        fun _ : ℝ => mexicanHat2D μSq lam v 0 := by
      ext α
      unfold mexicanHat2D
      have hcirc : (v * Real.cos α) ^ 2 + (v * Real.sin α) ^ 2 = v ^ 2 + 0 ^ 2 := by
        calc
          (v * Real.cos α) ^ 2 + (v * Real.sin α) ^ 2
              = v ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) := by ring
          _ = v ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq]
          _ = v ^ 2 + 0 ^ 2 := by ring
      rw [hcirc]
    rw [hev]
    exact hasDerivAt_const θ (mexicanHat2D μSq lam v 0)
  · intro μSq lam v h hvev
    unfold mexicanHat2D
    rw [← hvev]
    ring
  · intro g c m hg
    field_simp [hg]
    ring
  · intro Λ m
    unfold njlBareEnergy
    ring_nf
  · intro M m hM hm
    have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
    have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
    have hm4 : 0 < m ^ 4 := by positivity
    have hy_pos : 0 < (M ^ 2 / m ^ 2) ^ 2 := by positivity
    have hlog_y := Real.log_le_sub_one_of_pos hy_pos
    have hlog_eq : Real.log ((M ^ 2 / m ^ 2) ^ 2) = -2 * Real.log (m ^ 2 / M ^ 2) := by
      have hinv : Real.log (M ^ 2 / m ^ 2) = -Real.log (m ^ 2 / M ^ 2) := by
        rw [← inv_div (m ^ 2) (M ^ 2), Real.log_inv]
      rw [Real.log_pow, Nat.cast_ofNat, hinv]
      ring
    have hineq : -(M ^ 4 / 2) ≤ dynamicalDoubleWell M m := by
      have hmul : m ^ 4 * (-2 * Real.log (m ^ 2 / M ^ 2)) ≤ m ^ 4 * ((M ^ 2 / m ^ 2) ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hlog_y, hlog_eq]) hm4.le
      have hsimp : m ^ 4 * ((M ^ 2 / m ^ 2) ^ 2 - 1) = M ^ 4 - m ^ 4 := by
        field_simp [hm]
      rw [hsimp] at hmul
      unfold dynamicalDoubleWell
      linarith
    have hiff : dynamicalDoubleWell M m = -(M ^ 4 / 2) ↔ m = M ∨ m = -M := by
      constructor
      · intro hEq
        have hsq : m ^ 2 = M ^ 2 := by
          by_contra hne
          have hy_ne : (M ^ 2 / m ^ 2) ^ 2 ≠ 1 := by
            intro hy1
            have hfrac : M ^ 2 / m ^ 2 = 1 := by
              nlinarith [div_pos hM2 hm2]
            exact hne (by field_simp [hm] at hfrac; exact hfrac.symm)
          have hlt := Real.log_lt_sub_one_of_pos hy_pos hy_ne
          have hmul : m ^ 4 * (-2 * Real.log (m ^ 2 / M ^ 2)) < m ^ 4 * ((M ^ 2 / m ^ 2) ^ 2 - 1) :=
            mul_lt_mul_of_pos_left (by linarith [hlt, hlog_eq]) hm4
          have hsimp : m ^ 4 * ((M ^ 2 / m ^ 2) ^ 2 - 1) = M ^ 4 - m ^ 4 := by
            field_simp [hm]
          rw [hsimp] at hmul
          unfold dynamicalDoubleWell at hEq
          linarith
        exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
      · rintro (rfl | rfl)
        · unfold dynamicalDoubleWell
          rw [div_self hM2.ne', Real.log_one]
          ring
        · unfold dynamicalDoubleWell
          have hneg : (-M) ^ 2 / M ^ 2 = 1 := by
            rw [neg_sq]; exact div_self hM2.ne'
          rw [hneg, Real.log_one]
          ring
    have hz_gt : -(M ^ 4 / 2) < dynamicalDoubleWell M 0 := by
      unfold dynamicalDoubleWell
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
      linarith [pow_pos hM 4]
    exact ⟨hineq, hiff, hz_gt⟩
  · intro M hM
    have hM0 : M ≠ 0 := ne_of_gt hM
    have hder1_at_M := dynamicalDoubleWell_deriv1 M hM hM0
    have hd1 : deriv (dynamicalDoubleWell M) M = 0 := by
      rw [hder1_at_M.deriv, div_self (pow_ne_zero 2 hM0), Real.log_one]
      ring
    have hev : deriv (dynamicalDoubleWell M) =ᶠ[nhds M]
        fun x : ℝ => 4 * x ^ 3 * Real.log (x ^ 2 / M ^ 2) := by
      filter_upwards [isOpen_ne.mem_nhds hM0] with x hx
      exact (dynamicalDoubleWell_deriv1 M hM hx).deriv
    have hm2 : M ^ 2 / M ^ 2 ≠ 0 := by rw [div_self (pow_ne_zero 2 hM0)]; exact one_ne_zero
    have hinner : HasDerivAt (fun x : ℝ => x ^ 2 / M ^ 2) ((2 * M) / M ^ 2) M :=
      ((hasDerivAt_pow 2 M).div_const (M ^ 2)).congr_deriv (by norm_num)
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 / M ^ 2))
        ((M ^ 2 / M ^ 2)⁻¹ * ((2 * M) / M ^ 2)) M :=
      ((Real.hasDerivAt_log hm2).comp M hinner).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    have hp3 : HasDerivAt (fun x : ℝ => 4 * x ^ 3) (4 * (3 * M ^ 2)) M :=
      ((hasDerivAt_pow 3 M).const_mul 4).congr_deriv (by ring)
    have hder2 : HasDerivAt (deriv (dynamicalDoubleWell M))
        ((4 * (3 * M ^ 2)) * Real.log (M ^ 2 / M ^ 2) +
          (4 * M ^ 3) * ((M ^ 2 / M ^ 2)⁻¹ * ((2 * M) / M ^ 2))) M :=
      (hp3.mul hlog).congr_of_eventuallyEq hev
    have hd2 : deriv (deriv (dynamicalDoubleWell M)) M = 8 * M ^ 2 := by
      rw [hder2.deriv, div_self (pow_ne_zero 2 hM0), Real.log_one, inv_one]
      field_simp [hM0]
      ring
    exact ⟨hd1, hd2, by rw [hd2]; positivity⟩
  · intro Λ hΛ
    have hden : 0 < 1 + Λ := by linarith
    have hlt : 1 / (1 + Λ) < 1 := (div_lt_one hden).mpr (by linarith)
    have hpos : 0 < 1 / (1 + Λ) := div_pos one_pos hden
    exact ⟨by linarith, by linarith⟩
  · intro B _ P hP A C m n hmn X
    refine ⟨?_, clTowerColimit_ι_comp hmn X⟩
    peirce_nf hP

/-- Radial 4D Euclidean 1-loop fermion-bubble effective-potential integrand
`2 u log (u + m²)` in radial squared momentum `u = k² ∈ [0, Λ²]`. -/
def fermionBubbleIntegrand (m u : ℝ) : ℝ :=
  2 * u * Real.log (u + m ^ 2)

/-- Exact antiderivative `(u² - m⁴) log (u + m²) - u² / 2 + m² u` of `fermionBubbleIntegrand`. -/
def fermionBubblePrimitive (m u : ℝ) : ℝ :=
  (u ^ 2 - m ^ 4) * Real.log (u + m ^ 2) - u ^ 2 / 2 + m ^ 2 * u

/-- Counterterm-subtracted 1-loop NJL fermion-bubble effective potential at Euclidean cutoff `Λ`:
`(∫₀^{Λ²} 2 u log(u+m²) du) - (Λ⁴ log(Λ²) - Λ⁴/2) - 2 m² Λ² + m⁴ log(Λ² / M²)`. -/
def renormalizedFermionPotential (Λ M m : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Λ ^ 2, fermionBubbleIntegrand m u) -
    (Λ ^ 4 * Real.log (Λ ^ 2) - Λ ^ 4 / 2) - 2 * m ^ 2 * Λ ^ 2 + m ^ 4 * Real.log (Λ ^ 2 / M ^ 2)

private lemma log_one_add_sandwich {x : ℝ} (hx : 0 < x) :
    -(x ^ 2 / 2) ≤ Real.log (1 + x) - x ∧ Real.log (1 + x) - x ≤ -(x ^ 2 / 2) + x ^ 3 / 3 := by
  let g₁ : ℝ → ℝ := fun t => Real.log (1 + t) - t + t ^ 2 / 2
  have hg₁_mono : MonotoneOn g₁ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · intro t ht
      have hpos : 0 < 1 + t := by linarith [Set.mem_Ici.mp ht]
      exact (((continuousAt_const.add continuousAt_id).log hpos.ne').sub continuousAt_id |>.add
        ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hpos : 0 < 1 + t := by linarith [Set.mem_Ioi.mp ht]
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := (hasDerivAt_id t).const_add 1
      have hlog := h1.log hpos.ne'
      have hp2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
      have hder : HasDerivAt g₁ (1 / (1 + t) - 1 + t) t :=
        ((hlog.sub (hasDerivAt_id t)).add hp2).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
      exact hder.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := Set.mem_Ioi.mp ht
      have hpos : 0 < 1 + t := by linarith
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := (hasDerivAt_id t).const_add 1
      have hlog := h1.log hpos.ne'
      have hp2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
      have hder : HasDerivAt g₁ (1 / (1 + t) - 1 + t) t :=
        ((hlog.sub (hasDerivAt_id t)).add hp2).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
      rw [hder.deriv]
      have hval : 1 / (1 + t) - 1 + t = t ^ 2 / (1 + t) := by
        field_simp [hpos.ne']
        ring
      rw [hval]
      exact div_nonneg (sq_nonneg t) hpos.le
  let g₂ : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hg₂_mono : MonotoneOn g₂ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · intro t ht
      have hpos : 0 < 1 + t := by linarith [Set.mem_Ici.mp ht]
      exact (((continuousAt_id.sub ((continuousAt_id.pow 2).div_const 2)).add
        ((continuousAt_id.pow 3).div_const 3)).sub
        ((continuousAt_const.add continuousAt_id).log hpos.ne')).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hpos : 0 < 1 + t := by linarith [Set.mem_Ioi.mp ht]
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := (hasDerivAt_id t).const_add 1
      have hlog := h1.log hpos.ne'
      have hp2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
      have hp3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (t ^ 2) t := by
        simpa using ((hasDerivAt_pow 3 t).div_const 3).congr_deriv (by ring)
      have hder : HasDerivAt g₂ (1 - t + t ^ 2 - 1 / (1 + t)) t :=
        ((((hasDerivAt_id t).sub hp2).add hp3).sub hlog).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
      exact hder.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := Set.mem_Ioi.mp ht
      have hpos : 0 < 1 + t := by linarith
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := (hasDerivAt_id t).const_add 1
      have hlog := h1.log hpos.ne'
      have hp2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
      have hp3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (t ^ 2) t := by
        simpa using ((hasDerivAt_pow 3 t).div_const 3).congr_deriv (by ring)
      have hder : HasDerivAt g₂ (1 - t + t ^ 2 - 1 / (1 + t)) t :=
        ((((hasDerivAt_id t).sub hp2).add hp3).sub hlog).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
      rw [hder.deriv]
      have hval : 1 - t + t ^ 2 - 1 / (1 + t) = t ^ 3 / (1 + t) := by
        field_simp [hpos.ne']
        ring
      rw [hval]
      exact div_nonneg (pow_nonneg ht0.le 3) hpos.le
  have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_refl 0)
  have hg₁_0 : g₁ 0 ≤ g₁ x := hg₁_mono h0_mem (Set.mem_Ici.mpr hx.le) hx.le
  have hg₂_0 : g₂ 0 ≤ g₂ x := hg₂_mono h0_mem (Set.mem_Ici.mpr hx.le) hx.le
  have h01 : g₁ 0 = 0 := by simp [g₁]
  have h02 : g₂ 0 = 0 := by simp [g₂]
  rw [h01] at hg₁_0
  rw [h02] at hg₂_0
  dsimp only [g₁] at hg₁_0
  dsimp only [g₂] at hg₂_0
  exact ⟨by linarith, by linarith⟩

/-- **Continuum 1-Loop `intervalIntegral` Derivation of `dynamicalDoubleWell` (`C-COND` #2 Discharge)**:
1. For any nonzero `m` and any `Λ : ℝ`, the 4D Euclidean 1-loop fermion radial integral evaluates via
   FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) to
   `fermionBubblePrimitive m (Λ²) - fermionBubblePrimitive m 0`;
2. After exact `Λ⁴ log Λ²`, `Λ⁴ / 2`, and `2 m² Λ²` counterterm subtraction plus scale renormalization
   `m⁴ log(Λ² / M²)`, `renormalizedFermionPotential Λ M m` converges in the UV continuum limit
   `Λ → ∞` directly to `dynamicalDoubleWell M m` (discharging the continuum regularized-bubble
   assumption in `C-COND`). -/
theorem fermionBubble_integral_and_continuum_doubleWell
    (M m : ℝ) (hM : 0 < M) (hm : m ≠ 0) :
    (∀ Λ : ℝ,
      ∫ u in (0 : ℝ)..Λ ^ 2, fermionBubbleIntegrand m u =
        fermionBubblePrimitive m (Λ ^ 2) - fermionBubblePrimitive m 0) ∧
    (∀ Λ : ℝ, 0 < Λ →
      renormalizedFermionPotential Λ M m =
        (Λ ^ 4 * Real.log (1 + m ^ 2 / Λ ^ 2) - m ^ 2 * Λ ^ 2) -
          m ^ 4 * Real.log (1 + m ^ 2 / Λ ^ 2) + m ^ 4 * Real.log (m ^ 2 / M ^ 2)) ∧
    Filter.Tendsto (fun Λ : ℝ => renormalizedFermionPotential Λ M m)
      Filter.atTop (nhds (dynamicalDoubleWell M m)) := by
  have hm2_pos : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hint_eval : ∀ Λ : ℝ,
      ∫ u in (0 : ℝ)..Λ ^ 2, fermionBubbleIntegrand m u =
        fermionBubblePrimitive m (Λ ^ 2) - fermionBubblePrimitive m 0 := by
    intro Λ
    have hIcc : Set.uIcc (0 : ℝ) (Λ ^ 2) = Set.Icc 0 (Λ ^ 2) := Set.uIcc_of_le (sq_nonneg Λ)
    have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (Λ ^ 2),
        HasDerivAt (fermionBubblePrimitive m) (fermionBubbleIntegrand m u) u := by
      intro u hu
      rw [hIcc] at hu
      have hpos : 0 < u + m ^ 2 := by linarith [hu.1, hm2_pos]
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - m ^ 4) (2 * u) u := by
        simpa using ((hasDerivAt_pow 2 u).sub_const (m ^ 4)).congr_deriv (by ring)
      have hadd : HasDerivAt (fun y : ℝ => y + m ^ 2) 1 u := by
        simpa using (hasDerivAt_id u).add_const (m ^ 2)
      have hlog := hadd.log hpos.ne'
      have hp2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) u u := by
        simpa using ((hasDerivAt_pow 2 u).div_const 2).congr_deriv (by ring)
      have hlin : HasDerivAt (fun y : ℝ => m ^ 2 * y) (m ^ 2) u := by
        simpa using (hasDerivAt_id u).const_mul (m ^ 2)
      have htot := ((h1.mul hlog).sub hp2).add hlin
      refine htot.congr_deriv ?_
      dsimp only [fermionBubbleIntegrand]
      have hfac : u ^ 2 - m ^ 4 = (u - m ^ 2) * (u + m ^ 2) := by ring
      rw [hfac]
      field_simp [hpos.ne']
      ring
    have hcont : ContinuousOn (fermionBubbleIntegrand m) (Set.uIcc 0 (Λ ^ 2)) := by
      intro u hu
      rw [hIcc] at hu
      have hpos : 0 < u + m ^ 2 := by linarith [hu.1, hm2_pos]
      exact ((continuousAt_const.mul continuousAt_id).mul
        ((continuousAt_id.add continuousAt_const).log hpos.ne')).continuousWithinAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hformula : ∀ Λ : ℝ, 0 < Λ →
      renormalizedFermionPotential Λ M m =
        (Λ ^ 4 * Real.log (1 + m ^ 2 / Λ ^ 2) - m ^ 2 * Λ ^ 2) -
          m ^ 4 * Real.log (1 + m ^ 2 / Λ ^ 2) + m ^ 4 * Real.log (m ^ 2 / M ^ 2) := by
    intro Λ hΛ
    have hΛ2_pos : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
    have hM2_pos : 0 < M ^ 2 := sq_pos_of_pos hM
    have hrat_pos : 0 < 1 + m ^ 2 / Λ ^ 2 := by positivity
    have hlog_add : Real.log (Λ ^ 2 + m ^ 2) = Real.log (Λ ^ 2) + Real.log (1 + m ^ 2 / Λ ^ 2) := by
      have hmul : Λ ^ 2 + m ^ 2 = Λ ^ 2 * (1 + m ^ 2 / Λ ^ 2) := by
        field_simp [hΛ2_pos.ne']
      rw [hmul, Real.log_mul hΛ2_pos.ne' hrat_pos.ne']
    have hlog_div : Real.log (Λ ^ 2 / M ^ 2) = Real.log (Λ ^ 2) - Real.log (M ^ 2) :=
      Real.log_div hΛ2_pos.ne' hM2_pos.ne'
    have hlog_mM : Real.log (m ^ 2 / M ^ 2) = Real.log (m ^ 2) - Real.log (M ^ 2) :=
      Real.log_div hm2_pos.ne' hM2_pos.ne'
    unfold renormalizedFermionPotential
    rw [hint_eval Λ]
    unfold fermionBubblePrimitive
    have h0 : 0 ^ 2 - m ^ 4 = -m ^ 4 := by ring
    rw [show (0 : ℝ) + m ^ 2 = m ^ 2 by ring, hlog_add, hlog_div, hlog_mM]
    ring
  have hbounds : ∀ᶠ Λ : ℝ in Filter.atTop,
      dynamicalDoubleWell M m - m ^ 6 / Λ ^ 2 ≤ renormalizedFermionPotential Λ M m ∧
      renormalizedFermionPotential Λ M m ≤ dynamicalDoubleWell M m + m ^ 6 / (3 * Λ ^ 2) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Λ hΛ
    rw [hformula Λ hΛ]
    have hx_pos : 0 < m ^ 2 / Λ ^ 2 := div_pos hm2_pos (sq_pos_of_pos hΛ)
    have hsand := log_one_add_sandwich hx_pos
    have hlog_nonneg : 0 ≤ Real.log (1 + m ^ 2 / Λ ^ 2) := Real.log_nonneg (by linarith)
    have hlog_le : Real.log (1 + m ^ 2 / Λ ^ 2) ≤ m ^ 2 / Λ ^ 2 := by
      have h1 : Real.log (1 + m ^ 2 / Λ ^ 2) ≤ 1 + m ^ 2 / Λ ^ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      linarith
    have hL4 : 0 ≤ Λ ^ 4 := pow_nonneg hΛ.le 4
    have hm4 : 0 ≤ m ^ 4 := by positivity
    have h_low1 := mul_le_mul_of_nonneg_left hsand.1 hL4
    have h_high1 := mul_le_mul_of_nonneg_left hsand.2 hL4
    have h_low2 := mul_le_mul_of_nonneg_left hlog_le hm4
    have h_high2 := mul_le_mul_of_nonneg_left hlog_nonneg hm4
    have hΛ_ne : Λ ≠ 0 := hΛ.ne'
    have hsq1 : Λ ^ 4 * -((m ^ 2 / Λ ^ 2) ^ 2 / 2) = -(m ^ 4 / 2) := by
      field_simp [hΛ_ne]
    have hsq2 : Λ ^ 4 * (-((m ^ 2 / Λ ^ 2) ^ 2 / 2) + (m ^ 2 / Λ ^ 2) ^ 3 / 3) =
        -(m ^ 4 / 2) + m ^ 6 / (3 * Λ ^ 2) := by
      field_simp [hΛ_ne]
    have hlinL : Λ ^ 4 * (Real.log (1 + m ^ 2 / Λ ^ 2) - m ^ 2 / Λ ^ 2) =
        Λ ^ 4 * Real.log (1 + m ^ 2 / Λ ^ 2) - m ^ 2 * Λ ^ 2 := by
      field_simp [hΛ_ne]
    have hm6_eq : m ^ 4 * (m ^ 2 / Λ ^ 2) = m ^ 6 / Λ ^ 2 := by
      field_simp [hΛ_ne]
    rw [hlinL, hsq1] at h_low1
    rw [hlinL, hsq2] at h_high1
    rw [hm6_eq] at h_low2
    rw [mul_zero] at h_high2
    unfold dynamicalDoubleWell
    exact ⟨by linarith, by linarith⟩
  have hinv_sq : Filter.Tendsto (fun Λ : ℝ => (Λ ^ 2)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hlow_t : Filter.Tendsto (fun Λ : ℝ => dynamicalDoubleWell M m - m ^ 6 / Λ ^ 2)
      Filter.atTop (nhds (dynamicalDoubleWell M m)) := by
    have h0 : Filter.Tendsto (fun Λ : ℝ => dynamicalDoubleWell M m - m ^ 6 * (Λ ^ 2)⁻¹)
        Filter.atTop (nhds (dynamicalDoubleWell M m - m ^ 6 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv_sq)
    simpa [div_eq_mul_inv] using h0
  have hhigh_t : Filter.Tendsto (fun Λ : ℝ => dynamicalDoubleWell M m + m ^ 6 / (3 * Λ ^ 2))
      Filter.atTop (nhds (dynamicalDoubleWell M m)) := by
    have h0 : Filter.Tendsto (fun Λ : ℝ => dynamicalDoubleWell M m + (m ^ 6 / 3) * (Λ ^ 2)⁻¹)
        Filter.atTop (nhds (dynamicalDoubleWell M m + (m ^ 6 / 3) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv_sq)
    simpa [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using h0
  have htend : Filter.Tendsto (fun Λ : ℝ => renormalizedFermionPotential Λ M m)
      Filter.atTop (nhds (dynamicalDoubleWell M m)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_t hhigh_t
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  exact ⟨hint_eval, hformula, htend⟩

end MA7_DynamicalVacuumMass

/-! ## Archetype Registrations (`MA₆`, `MA₇`) -/

section ArchetypeRegistrations

/-- Proved `TypedArchetype` for `MA₆`: Majorana/Weyl circular split-octonion spinor basis,
spectral noncommutative AKNS–Lax coupled NLS theorem, complex `M₂(ℂ)` correspondence, and
Dirac–Zorn birefringent cubic decomposition. -/
def archMA6ChiralFluidNLSLax : TypedArchetype Unit .proved where
  name := `archMA6ChiralFluidNLSLax
  phase := 6
  claim := fun _ =>
    (Function.Injective operatorFrame ∧ Eplus ≠ Eminus) ∧
    (∀ {R B : Type} [CommRing R] [Ring B] [Algebra R B] {P : B}, P * P = P →
      ∀ (ζ : R) (A C Ax Cx Axx Cxx At Ct : B),
      chiralLaxCurvature P A C Ax Cx Axx Cxx At Ct ζ =
        nlsPlusResidual P A C Axx At + nlsMinusResidual P A C Cxx Ct) ∧
    (∀ spectral q r qx rx qxx rxx qt rt : ℂ,
      Complex.I • chiralLaxCurvature projMat2 (upperMat2 q) (lowerMat2 r)
          (upperMat2 qx) (lowerMat2 rx) (upperMat2 qxx) (lowerMat2 rxx)
          (upperMat2 (-Complex.I * qt)) (lowerMat2 (-Complex.I * rt)) (-Complex.I * spectral) =
        InfoGeometry.Physics.CubicNLSAKNSLaxPair.curvature spectral q r qx rx qt rt qxx rxx) ∧
    (∀ (u₁ u₂ u₃ v₁ v₂ v₃ : ℝ),
      manakovKerrEnergy (1 : ℝ) 1 = 4 ∧
      (diracZornOp (0 : ℝ) 0 u₁ u₂ u₃ v₁ v₂ v₃ * diracZornOp (0 : ℝ) 0 u₁ u₂ u₃ v₁ v₂ v₃) 0 0 =
        fiberEmbed (zornDot u₁ u₂ u₃ v₁ v₂ v₃) +
          vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃) (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃) (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃))
  evidence := fun _ =>
    ⟨⟨chiral_fluid_majorana_weyl_circular_basis.2.1.1,
      chiral_fluid_majorana_weyl_circular_basis.2.1.2.1⟩,
     fun hP ζ A C Ax Cx Axx Cxx At Ct =>
       (noncommutative_chiral_akns_lax_and_coupled_nls hP ζ A C Ax Cx Axx Cxx At Ct).1,
     fun spectral q r qx rx qxx rxx qt rt =>
       (chiral_akns_lax_matrix2_complex_correspondence spectral q r qx rx qxx rxx qt rt).2.2.2,
     fun u₁ u₂ u₃ v₁ v₂ v₃ =>
       let h := diracZorn_birefringent_cubic_and_manakov_xpm ℝ u₁ u₂ u₃ v₁ v₂ v₃
       ⟨h.2.2.2, h.1⟩⟩

/-- Proved `TypedArchetype` for `MA₇`: Goldstone–Higgs shift, NJL `Λ²` counterterm cancellation,
Mannheim scale-free dynamical double-well global minimum (`-M⁴ / 2` at `m = ±M`, curvature `8 M²`),
and `ClTowerColimit` chiral condensate mass. -/
def archMA7DynamicalVacuumMass : TypedArchetype Unit .proved where
  name := `archMA7DynamicalVacuumMass
  phase := 7
  claim := fun _ =>
    (∀ μSq lam v θ : ℝ,
      HasDerivAt (fun α : ℝ => mexicanHat2D μSq lam (v * Real.cos α) (v * Real.sin α)) 0 θ) ∧
    (∀ M m : ℝ, 0 < M → m ≠ 0 →
      Filter.Tendsto (fun Λ : ℝ => renormalizedFermionPotential Λ M m)
        Filter.atTop (nhds (dynamicalDoubleWell M m)) ∧
      -(M ^ 4 / 2) ≤ dynamicalDoubleWell M m ∧
      (dynamicalDoubleWell M m = -(M ^ 4 / 2) ↔ m = M ∨ m = -M)) ∧
    (∀ M : ℝ, 0 < M →
      deriv (dynamicalDoubleWell M) M = 0 ∧
      deriv (deriv (dynamicalDoubleWell M)) M = 8 * M ^ 2) ∧
    (∀ {B : Type} [Ring B] {P : B}, P * P = P → ∀ A C : B, genPhi P A C * genPhi P A C = genV P A C)
  evidence := fun _ =>
    let h := dynamical_mass_goldstone_njl_and_vacuum_doublewell
    ⟨h.1,
     fun M m hM hm =>
       ⟨(fermionBubble_integral_and_continuum_doubleWell M m hM hm).2.2,
        (h.2.2.2.2.1 M m hM hm).1, (h.2.2.2.2.1 M m hM hm).2.1⟩,
     fun M hM => ⟨(h.2.2.2.2.2.1 M hM).1, (h.2.2.2.2.2.1 M hM).2.1⟩,
     fun hP A C => (h.2.2.2.2.2.2.2 hP A C 0 0 (le_refl 0) 0).1⟩

#register_archetype archMA6ChiralFluidNLSLax
#audit_archetype archMA6ChiralFluidNLSLax
#register_archetype archMA7DynamicalVacuumMass
#audit_archetype archMA7DynamicalVacuumMass

end ArchetypeRegistrations

end InfoGeometry.Algebra.ChiralFluidNLSLaxAndDynamicalVacuumMass
