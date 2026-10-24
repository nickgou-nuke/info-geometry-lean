/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability
import InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
import InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

/-!
# Five-Stream Master Intertwiner: Unifying Grassmannian Geometry, Moebius–Bruhat Flows, KMS Operator Algebras, Parabolic Modular Cyclotomics, and De Bruijn Rotor Alternation

The canonical contracts below are carrier equality, Peirce-corner extraction,
polynomial rotor identities, and tracial linear-functional identities. The legacy
stream names do not add principal-bundle, metric, or analytic KMS assertions.

This module connects and intertwines all five canonical streams over a single
algebraic carrier `[CommRing R] [Ring A] [Algebra R A]` and dual root-of-zero pair `(d, B)`:

1. **Stream 1 (`GrassmannianBundleCyclotomicOrientability`)** $\leftrightarrow$ **Stream 5 (`DeBruijnRotorAlternationCycle`)**:
   - The moving pole projector `P₊(c, s) = R(c, s) P₊ R(c, -s)` is definitionally the
     Stream 1 homogeneous Grassmannian projection `homogeneousProj (R(c, s)) (R(c, -s)) P₊`
     and is an exact idempotent point `IsIdempotentElem (P₊(c, s))` whenever `c² + s² = 1`.
   - At the Grassmannian basepoint `P₊ = d B`, Stream 1's `cotangentNilpotent P₊ d = d`,
     `tangentNilpotent P₊ B = B`, and `normalBundlePart P₊ Q₁ = 0` (the Stream 5 turning
     velocity `Q₁ = d + B` is purely horizontal/off-diagonal in the Stream 1 Peirce bundle).
2. **Stream 2 (`RootsOfZeroUnityMoebiusModularG22`)** & **Stream 4 (`ModularParabolicCyclotomicSynthesis`)**
   $\leftrightarrow$ **Stream 5 (`DeBruijnRotorAlternationCycle`)**:
   - At the quarter-turn `(c, s) = (0, 1)`, Stream 5's algebraic rotor `R(0, 1)` coincides
     with Stream 4's triple parabolic shear `bruhatQuarticOp d B = (1 + d)(1 - B)(1 + d)`,
     Stream 2's `moebiusWeylInversion d B`, and Stream 3's `bruhatWeylReflection d B`.
   - Conjugating Stream 5's oscillator `(Γ, J)` by Stream 4's `w_J = bruhatQuarticOp d B`
     reverses the polarization (`w_J * Γ * w_J⁻¹ = -Γ`) while fixing the wheel generator
     (`w_J * J * w_J⁻¹ = J`), and the shared modular center `Λ₆³ = w_J² = P₀ - Δ` acts as
     `-1` on both `Γ` and `J`.
3. **Stream 3 (`UnifiedGeometryOperatorSignificance`)** & **Stream 4 (`ModularParabolicCyclotomicSynthesis`)**
   $\leftrightarrow$ **Stream 5 (`DeBruijnRotorAlternationCycle`)**:
   - Every tracial linear functional `τ : A →ₗ[R] R` automatically vanishes on the off-diagonal
     nilpotent seeds (`τ d = 0` and `τ B = 0`), so the Stream 3 KMS-weighted trace of Stream 5's
     moving projector `P₊(c, s)` satisfies the exact quadratic interpolation law:
     `τ (kmsModularWeight u v d B * movingPolePlus c s d B) = (v * v * (c * c)) * τ P₊ + (u * u * (s * s)) * τ P₋`.
   - Stream 3/4's Jordan left-multiplication commutator `[L_d, L_B] ∈ Module.End R A`
     intertwines Stream 5's transition velocity `Q₁ = d + B` and wheel generator `J = d - B`:
     `([L_d, L_B]) Q₁ = 2 • J` and `([L_d, L_B]) J = 2 • Q₁`.
4. **Diamond Causal Poset (`FiveStreamIntertwinerArchetype`) & Meta Epistemic Compiler**:
   - Certifies the 4-node cross-stream diamond poset via `#register_archetype`,
     `#audit_archetype`, `compile`, and `executable_certified_compilation`.
-/

namespace InfoGeometry.Canonical.FiveStreamMasterIntertwiner

open Matrix
open InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability
open InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22
open InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
open InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

section CrossStreamIntertwiners

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
## 1. Node 0: Cross-Stream Carrier Identity & Stream 1 Grassmannian Bundle Extraction
-/

/-- Bridge predicate Equivalence: Stream 4's `IsDualRootOfZeroPair d B` and Stream 5's
    `IsDualSeedPair d B` are equivalent. -/
lemma isDualRootOfZeroPair_iff_isDualSeedPair (d B : A) :
    IsDualRootOfZeroPair d B ↔ IsDualSeedPair d B :=
  ⟨fun h => ⟨h.d_sq, h.B_sq, h.dBd, h.BdB⟩,
   fun h => ⟨h.d_sq, h.B_sq, h.dBd, h.BdB⟩⟩

/-- Definitional unification of the carriers across Streams 2, 3, 4, and 5:
    the positive/negative poles, active support, harmonic zero-mode, chiral polarization /
    Ehresmann curvature, and Weyl reflection coincide definitionally. -/
theorem cross_stream_definitional_carrier_coherence (d B : A) :
    DeBruijnRotorAlternationCycle.polePlus d B =
      UnifiedGeometryOperatorSignificance.projPlus d B ∧
    DeBruijnRotorAlternationCycle.poleMinus d B =
      UnifiedGeometryOperatorSignificance.projMinus d B ∧
    DeBruijnRotorAlternationCycle.carrierSupport d B =
      UnifiedGeometryOperatorSignificance.hodgeLaplacian d B ∧
    DeBruijnRotorAlternationCycle.zeroModeSupport d B =
      UnifiedGeometryOperatorSignificance.projHarmonic d B ∧
    DeBruijnRotorAlternationCycle.phasePolarization d B =
      UnifiedGeometryOperatorSignificance.ehresmannCurvature d B ∧
    DeBruijnRotorAlternationCycle.wheelGenerator d B =
      UnifiedGeometryOperatorSignificance.kahlerStructure d B ∧
    RootsOfZeroUnityMoebiusModularG22.moebiusWeylInversion d B =
      UnifiedGeometryOperatorSignificance.bruhatWeylReflection d B :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Stream 5's moving pole `movingPolePlus c s d B` is definitionally Stream 1's
    `homogeneousProj (phaseRotor c s d B) (phaseRotor c (-s) d B) (polePlus d B)` and is
    an idempotent Grassmannian point (`IsIdempotentElem`) whenever `c * c + s * s = 1`. -/
theorem movingPolePlus_is_grassmannian_homogeneousProj {d B : A}
    (h : IsDualSeedPair d B) (c s : R) (hcs : c * c + s * s = 1) :
    movingPolePlus c s d B =
      homogeneousProj (phaseRotor c s d B) (phaseRotor c (-s) d B)
        (DeBruijnRotorAlternationCycle.polePlus d B) ∧
    IsIdempotentElem (movingPolePlus c s d B) :=
  ⟨rfl, movingPolePlus_idem h c s hcs⟩

/-- Stream 1's Grassmannian cotangent and tangent nilpotent projections at `P₊ = d B`
    extract the Stream 5 seeds `d` and `B`, both individually and from `Q₁ = d + B`. -/
lemma grassmannian_peirce_tangent_cotangent_seeds {d B : A} (h : IsDualSeedPair d B) :
    let P := DeBruijnRotorAlternationCycle.polePlus d B
    cotangentNilpotent P d = d ∧
    tangentNilpotent P B = B ∧
    tangentNilpotent P (transitionVelocity d B) = B ∧
    cotangentNilpotent P (transitionVelocity d B) = d := by
  intro P
  have hd_P : d * P = 0 := by unfold P DeBruijnRotorAlternationCycle.polePlus; rw [← mul_assoc, h.d_sq, zero_mul]
  have hP_d : P * d = d := h.dBd
  have hP_B : P * B = 0 := by unfold P DeBruijnRotorAlternationCycle.polePlus; rw [mul_assoc, h.B_sq, mul_zero]
  have hB_P : B * P = B := by unfold P DeBruijnRotorAlternationCycle.polePlus; rw [← mul_assoc, h.BdB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cotangentNilpotent; rw [hP_d, mul_sub, mul_one, hd_P, sub_zero]
  · unfold tangentNilpotent; rw [sub_mul, one_mul, hP_B, sub_zero, hB_P]
  · unfold tangentNilpotent transitionVelocity
    rw [mul_add, add_mul, sub_mul, one_mul, hP_d, sub_self, zero_mul, zero_add,
        sub_mul, one_mul, hP_B, sub_zero, hB_P]
  · unfold cotangentNilpotent transitionVelocity
    rw [mul_add, add_mul, hP_d, hP_B, zero_mul, add_zero, mul_sub, mul_one, hd_P, sub_zero]

/-- Stream 1's Grassmannian Peirce decomposition at `P₊ = d B` extracts the Stream 5
    seed `d` as the upper cotangent nilpotent corner, `B` as the lower tangent nilpotent
    corner, and annihilates `Q₁ = d + B` on the diagonal normal bundle (`normalBundlePart P₊ Q₁ = 0`). -/
theorem grassmannian_peirce_extracts_seeds_and_horizontal_velocity {d B : A}
    (h : IsDualSeedPair d B) :
    let P := DeBruijnRotorAlternationCycle.polePlus d B
    cotangentNilpotent P d = d ∧
    tangentNilpotent P B = B ∧
    normalBundlePart P (transitionVelocity d B) = 0 := by
  intro P
  obtain ⟨hd, hB, h_tan, h_cot⟩ := grassmannian_peirce_tangent_cotangent_seeds h
  refine ⟨hd, hB, ?_⟩
  have h_decomp := normal_tangent_cotangent_decomp P (transitionVelocity d B)
  calc normalBundlePart P (transitionVelocity d B)
    _ = (normalBundlePart P (transitionVelocity d B) + tangentNilpotent P (transitionVelocity d B) +
         cotangentNilpotent P (transitionVelocity d B)) - B - d := by
        rw [h_tan, h_cot]; abel
    _ = 0 := by rw [h_decomp]; unfold transitionVelocity; abel

/-- Multiplicative orthogonality, squared displacement, and compression for
moving idempotents. The cross-stream carrier equality is algebraic; no metric,
Mostow decomposition, or Born probability is asserted. -/
theorem movingPoles_chordal_compression_and_orthogonality {d B : A}
    (h : IsDualSeedPair d B) {c s : R} (h_cs : c * c + s * s = 1) :
    movingPolePlus c s d B * movingPoleMinus c s d B = 0 ∧
    (movingPolePlus c s d B - DeBruijnRotorAlternationCycle.polePlus d B) *
      (movingPolePlus c s d B - DeBruijnRotorAlternationCycle.polePlus d B) =
      (s * s) • hodgeLaplacian d B ∧
    DeBruijnRotorAlternationCycle.polePlus d B * movingPolePlus c s d B *
      DeBruijnRotorAlternationCycle.polePlus d B =
      (c * c) • DeBruijnRotorAlternationCycle.polePlus d B :=
  ⟨(movingPoles_complementary_idempotents h h_cs).2.2.2.1,
   (movingPolePlus_chordal_square_and_compression h h_cs).1,
   (movingPolePlus_chordal_square_and_compression h h_cs).2⟩

/-!
## 2. Node 1: Stream 4 Parabolic Modular Shears Intertwine Stream 5 Rotor Oscillator
-/

/-- At the quarter-turn `(c, s) = (0, 1)`, Stream 5's algebraic rotor `phaseRotor 0 1 d B`
    equals Stream 4's triple parabolic shear `bruhatQuarticOp d B = (1 + d)(1 - B)(1 + d)`,
    Stream 2's `moebiusWeylInversion d B`, and Stream 3's `bruhatWeylReflection d B`. -/
theorem phaseRotor_quarter_turn_eq_bruhatQuarticOp {d B : A} (h : IsDualSeedPair d B) :
    phaseRotor (0 : R) (1 : R) d B = bruhatQuarticOp d B ∧
    phaseRotor (0 : R) (1 : R) d B = moebiusWeylInversion d B ∧
    phaseRotor (0 : R) (1 : R) d B = bruhatWeylReflection d B := by
  have h4 : IsDualRootOfZeroPair d B := (isDualRootOfZeroPair_iff_isDualSeedPair d B).mpr h
  have h_rotor : phaseRotor (0 : R) (1 : R) d B =
      zeroModeSupport d B + wheelGenerator d B := by
    unfold phaseRotor
    rw [zero_smul, one_smul, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [h_rotor, bruhatQuarticOp_eq_zeroMode_add_sub h4]
    rfl
  · rw [h_rotor]
    rfl
  · rw [h_rotor]
    rfl

/-- Stream 4's `activeSupport d B` acts as identity on Stream 5's poles and wheel generator,
    while `poleZeroMode d B` annihilates them. -/
lemma activeSupport_and_zeroMode_on_oscillator {d B : A} (h : IsDualSeedPair d B) :
    poleZeroMode d B * phasePolarization d B = 0 ∧
    ModularParabolicCyclotomicSynthesis.activeSupport d B * phasePolarization d B =
      phasePolarization d B ∧
    poleZeroMode d B * wheelGenerator d B = 0 ∧
    ModularParabolicCyclotomicSynthesis.activeSupport d B * wheelGenerator d B =
      wheelGenerator d B := by
  have h4 : IsDualRootOfZeroPair d B := (isDualRootOfZeroPair_iff_isDualSeedPair d B).mpr h
  have hP0_Pp : poleZeroMode d B * DeBruijnRotorAlternationCycle.polePlus d B = 0 :=
    RootsOfZeroUnityMoebiusModularG22.harmonicZeroPole_mul_polePlus h.d_sq h.dBd
  have hP0_Pm : poleZeroMode d B * DeBruijnRotorAlternationCycle.poleMinus d B = 0 :=
    RootsOfZeroUnityMoebiusModularG22.harmonicZeroPole_mul_poleMinus h.B_sq h.BdB
  have hP0_G : poleZeroMode d B * phasePolarization d B = 0 := by
    unfold phasePolarization; rw [mul_sub, hP0_Pp, hP0_Pm, sub_zero]
  have hP0_J : poleZeroMode d B * wheelGenerator d B = 0 :=
    ModularParabolicCyclotomicSynthesis.poleZeroMode_mul_hodgeDiff h4
  have hDelta_eq : ModularParabolicCyclotomicSynthesis.activeSupport d B = 1 - poleZeroMode d B := by
    unfold poleZeroMode; abel
  refine ⟨hP0_G, ?_, hP0_J, ?_⟩
  · rw [hDelta_eq, sub_mul, one_mul, hP0_G, sub_zero]
  · rw [hDelta_eq, sub_mul, one_mul, hP0_J, sub_zero]

/-- Stream 4's shared modular center involution `Λ₆³ = w_J² = P₀ - Δ` acts as `-1`
    on both Stream 5's `phasePolarization d B` (`Γ = P₊ - P₋`) and `wheelGenerator d B` (`J = d - B`). -/
theorem modular_center_acts_as_minus_one_on_oscillator {d B : A} (h : IsDualSeedPair d B) :
    parabolicHexalityOp d B ^ 3 * phasePolarization d B = -phasePolarization d B ∧
    parabolicHexalityOp d B ^ 3 * wheelGenerator d B = -wheelGenerator d B := by
  have h4 : IsDualRootOfZeroPair d B := (isDualRootOfZeroPair_iff_isDualSeedPair d B).mpr h
  obtain ⟨hP0_G, hDelta_G, hP0_J, hDelta_J⟩ := activeSupport_and_zeroMode_on_oscillator h
  rw [parabolicHexalityOp_cube h4]
  refine ⟨?_, ?_⟩
  · rw [sub_mul, hP0_G, hDelta_G, zero_sub]
  · rw [sub_mul, hP0_J, hDelta_J, zero_sub]

/-- Stream 2/4's Bruhat Weyl inversion `w_J = bruhatQuarticOp d B` conjugates Stream 5's
    `phasePolarization d B` (`Γ = P₊ - P₋`) to `-Γ`. -/
theorem bruhatQuarticOp_reverses_phasePolarization {d B : A} (h : IsDualSeedPair d B) :
    bruhatQuarticOp d B * phasePolarization d B * bruhatQuarticOpInv d B =
      -phasePolarization d B := by
  have h_eq_w : bruhatQuarticOp d B = bruhatWeylReflection d B :=
    UnifiedGeometryOperatorSignificance.bruhat_triple_product h.d_sq h.dBd
  have h_eq_inv : bruhatQuarticOpInv d B = bruhatWeylReflectionInv d B :=
    ModularParabolicCyclotomicSynthesis.bruhatQuarticOpInv_eq_zeroMode_sub_sub
      ((isDualRootOfZeroPair_iff_isDualSeedPair d B).mpr h)
  rw [h_eq_w, h_eq_inv]
  unfold phasePolarization
  calc bruhatWeylReflection d B *
       (DeBruijnRotorAlternationCycle.polePlus d B - DeBruijnRotorAlternationCycle.poleMinus d B) *
       bruhatWeylReflectionInv d B
    _ = bruhatWeylReflection d B * projPlus d B * bruhatWeylReflectionInv d B -
        bruhatWeylReflection d B * projMinus d B * bruhatWeylReflectionInv d B := by
        change bruhatWeylReflection d B * (projPlus d B - projMinus d B) * bruhatWeylReflectionInv d B = _
        noncomm_ring
    _ = -(DeBruijnRotorAlternationCycle.polePlus d B - DeBruijnRotorAlternationCycle.poleMinus d B) := by
        rw [bruhatWeylReflection_conj_projPlus h.d_sq h.B_sq h.dBd h.BdB,
            bruhatWeylReflection_conj_projMinus h.d_sq h.B_sq h.dBd h.BdB]
        change projMinus d B - projPlus d B = -(projPlus d B - projMinus d B)
        abel

/-!
## 3. Node 2: Stream 3 KMS Modular Trace & Stream 4 Jordan-Lie Lift on Stream 5 Rotor
-/

/-- **Automatic Tracial Vanishing on Nilpotent Seeds (`tracial_vanishes_on_dual_seeds`)**:
    For any tracial linear map `τ : A →ₗ[R] R` (`∀ x y, τ (x * y) = τ (y * x)`),
    `τ d = 0` and `τ B = 0` hold automatically without extra hypotheses. -/
theorem tracial_vanishes_on_dual_seeds {d B : A} (h : IsDualSeedPair d B)
    (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x)) :
    τ d = 0 ∧ τ B = 0 := by
  refine ⟨?_, ?_⟩
  · calc τ d = τ ((d * B) * d) := by rw [h.dBd]
      _ = τ (d * (d * B)) := hτ (d * B) d
      _ = 0 := by rw [← mul_assoc, h.d_sq, zero_mul, map_zero]
  · calc τ B = τ ((B * d) * B) := by rw [h.BdB]
      _ = τ (B * (B * d)) := hτ (B * d) B
      _ = 0 := by rw [← mul_assoc, h.B_sq, zero_mul, map_zero]

/-- Product of Stream 3's `kmsModularWeight u v d B = (u * u) • P₋ + (v * v) • P₊`
    with Stream 5's moving pole `movingPolePlus c s d B`. -/
lemma kmsModularWeight_mul_movingPolePlus {d B : A} (h : IsDualSeedPair d B) (u v c s : R) :
    kmsModularWeight u v d B * movingPolePlus c s d B =
      (v * v * (c * c)) • DeBruijnRotorAlternationCycle.polePlus d B +
      (u * u * (s * s)) • DeBruijnRotorAlternationCycle.poleMinus d B -
      (v * v * (c * s)) • d -
      (u * u * (c * s)) • B := by
  have h_kms : kmsModularWeight u v d B =
      (u * u) • DeBruijnRotorAlternationCycle.poleMinus d B +
      (v * v) • DeBruijnRotorAlternationCycle.polePlus d B := rfl
  have hPm_Q1 : DeBruijnRotorAlternationCycle.poleMinus d B * transitionVelocity d B = B := by
    unfold DeBruijnRotorAlternationCycle.poleMinus transitionVelocity
    rw [mul_add, mul_assoc, h.d_sq, mul_zero, zero_add, h.BdB]
  have hPp_Q1 : DeBruijnRotorAlternationCycle.polePlus d B * transitionVelocity d B = d := by
    unfold DeBruijnRotorAlternationCycle.polePlus transitionVelocity
    rw [mul_add, h.dBd, mul_assoc, h.B_sq, mul_zero, add_zero]
  rw [h_kms, (movingPolePlus_explicit_formula h c s).1,
      mul_sub, mul_add, add_mul, add_mul, add_mul,
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, mul_smul_comm, mul_smul_comm,
      mul_smul_comm, mul_smul_comm, mul_smul_comm,
      DeBruijnRotorAlternationCycle.poleMinus_mul_polePlus h,
      DeBruijnRotorAlternationCycle.polePlus_idem h,
      DeBruijnRotorAlternationCycle.poleMinus_idem h,
      DeBruijnRotorAlternationCycle.polePlus_mul_poleMinus h,
      hPm_Q1, hPp_Q1]
  simp only [smul_zero, zero_add, add_zero, smul_smul]
  abel

/-- **KMS-Weighted Tracial Interpolation of the Moving Rotor Projector**:
    Under any tracial linear map `τ : A →ₗ[R] R`, the off-diagonal turning velocity `-c s Q₁`
    has zero KMS-weighted trace, so `τ (kmsModularWeight u v d B * movingPolePlus c s d B)`
    is the exact quadratic combination `(v * v * (c * c)) * τ P₊ + (u * u * (s * s)) * τ P₋`. -/
theorem tracial_kms_movingPolePlus_interpolation {d B : A} (h : IsDualSeedPair d B)
    (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x)) (u v c s : R) :
    τ (kmsModularWeight u v d B * movingPolePlus c s d B) =
      (v * v * (c * c)) * τ (DeBruijnRotorAlternationCycle.polePlus d B) +
      (u * u * (s * s)) * τ (DeBruijnRotorAlternationCycle.poleMinus d B) := by
  obtain ⟨hτd, hτB⟩ := tracial_vanishes_on_dual_seeds h τ hτ
  rw [kmsModularWeight_mul_movingPolePlus h u v c s, map_sub, map_sub, map_add,
      map_smul, map_smul, map_smul, map_smul, hτd, hτB]
  simp only [smul_eq_mul, mul_zero, sub_zero]

/-- **Jordan Left-Multiplication Commutator Intertwines Stream 5 Velocity & Wheel**:
    The associative Jordan multiplication commutator `[L_d, L_B] ∈ Module.End R A` from
    Stream 3/4 acts as the hyperbolic partner of Stream 5's `ad_J`:
    `([L_d, L_B]) Q₁ = 2 • J` and `([L_d, L_B]) J = 2 • Q₁`. -/
theorem jordanLeft_commutator_intertwines_velocity_and_wheel {d B : A} (h : IsDualSeedPair d B) :
    (InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) d *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) B -
     InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) B *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) d)
      (transitionVelocity d B) = 2 • wheelGenerator d B ∧
    (InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) d *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) B -
     InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) B *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) d)
      (wheelGenerator d B) = 2 • transitionVelocity d B := by
  rw [InfoGeometry.Core.JordanMultiplicationClosure.commutator_apply,
      InfoGeometry.Core.JordanMultiplicationClosure.commutator_apply]
  have h_comm_d : (d * B - B * d) * d - d * (d * B - B * d) = 2 • d :=
    UnifiedGeometryOperatorSignificance.lieBracket_ehresmann_d h.d_sq h.dBd
  have h_comm_B : (d * B - B * d) * B - B * (d * B - B * d) = -(2 • B) :=
    UnifiedGeometryOperatorSignificance.lieBracket_ehresmann_B h.B_sq h.BdB
  refine ⟨?_, ?_⟩
  · unfold transitionVelocity wheelGenerator
    calc (d * B - B * d) * (d + B) - (d + B) * (d * B - B * d)
      _ = ((d * B - B * d) * d - d * (d * B - B * d)) +
          ((d * B - B * d) * B - B * (d * B - B * d)) := by noncomm_ring
      _ = 2 • (d - B) := by rw [h_comm_d, h_comm_B, smul_sub]; abel
  · unfold transitionVelocity wheelGenerator
    calc (d * B - B * d) * (d - B) - (d - B) * (d * B - B * d)
      _ = ((d * B - B * d) * d - d * (d * B - B * d)) -
          ((d * B - B * d) * B - B * (d * B - B * d)) := by noncomm_ring
      _ = 2 • (d + B) := by rw [h_comm_d, h_comm_B, smul_add]; abel

/-!
## 4. Node 3: Five-Stream Master Synthesis Theorem
-/

/-- **Five-Stream Master Intertwining Theorem**:
    Simultaneously connects:
    1. Stream 1 Grassmannian homogeneous projection & tangent/cotangent seed extraction,
    2. Stream 2/4 Tits–Bruhat–Moufang Weyl inversion and parabolic hexality center `Λ₆³ = w_J²`,
    3. Stream 3 KMS-weighted tracial rotor interpolation and Jordan `[L_d, L_B]` velocity/wheel swap,
    4. Stream 5 algebraic rotor idempotence and carrier conservation. -/
theorem five_stream_master_intertwining_theorem {d B : A}
    (h : IsDualSeedPair d B)
    (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    (u v c s : R) (hcs : c * c + s * s = 1) :
    (IsIdempotentElem (movingPolePlus c s d B) ∧
     cotangentNilpotent (DeBruijnRotorAlternationCycle.polePlus d B) d = d ∧
     tangentNilpotent (DeBruijnRotorAlternationCycle.polePlus d B) B = B ∧
     normalBundlePart (DeBruijnRotorAlternationCycle.polePlus d B) (transitionVelocity d B) = 0) ∧
    (phaseRotor (0 : R) (1 : R) d B = bruhatQuarticOp d B ∧
     bruhatQuarticOp d B * phasePolarization d B * bruhatQuarticOpInv d B = -phasePolarization d B ∧
     parabolicHexalityOp d B ^ 3 * wheelGenerator d B = -wheelGenerator d B) ∧
    (τ (kmsModularWeight u v d B * movingPolePlus c s d B) =
       (v * v * (c * c)) * τ (DeBruijnRotorAlternationCycle.polePlus d B) +
       (u * u * (s * s)) * τ (DeBruijnRotorAlternationCycle.poleMinus d B) ∧
     (InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) d *
        InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) B -
      InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) B *
        InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) d)
       (transitionVelocity d B) = 2 • wheelGenerator d B) :=
  ⟨⟨(movingPolePlus_is_grassmannian_homogeneousProj h c s hcs).2,
    (grassmannian_peirce_extracts_seeds_and_horizontal_velocity h).1,
    (grassmannian_peirce_extracts_seeds_and_horizontal_velocity h).2.1,
    (grassmannian_peirce_extracts_seeds_and_horizontal_velocity h).2.2⟩,
   ⟨(phaseRotor_quarter_turn_eq_bruhatQuarticOp h).1,
    bruhatQuarticOp_reverses_phasePolarization h,
    (modular_center_acts_as_minus_one_on_oscillator h).2⟩,
   ⟨tracial_kms_movingPolePlus_interpolation h τ hτ u v c s,
    (jordanLeft_commutator_intertwines_velocity_and_wheel h).1⟩⟩

end CrossStreamIntertwiners

/-!
## 5. Concrete Noncommutative Matrix Witness in `Matrix (Fin 2) (Fin 2) ℤ`
-/

section ConcreteMatrixWitness

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Concrete non-vacuity witness in `Matrix (Fin 2) (Fin 2) ℤ` verifying the 5-stream
    intertwining identities on `seedD = E₀₁` and `seedB = E₁₀`. -/
theorem mat2Z_five_stream_intertwiner_witness :
    seedD * seedB ≠ seedB * seedD ∧
    phaseRotor (0 : ℤ) (1 : ℤ) seedD seedB = bruhatQuarticOp seedD seedB ∧
    cotangentNilpotent (DeBruijnRotorAlternationCycle.polePlus seedD seedB) seedD = seedD ∧
    tangentNilpotent (DeBruijnRotorAlternationCycle.polePlus seedD seedB) seedB = seedB ∧
    normalBundlePart (DeBruijnRotorAlternationCycle.polePlus seedD seedB)
      (transitionVelocity seedD seedB) = 0 ∧
    bruhatQuarticOp seedD seedB * phasePolarization seedD seedB *
      bruhatQuarticOpInv seedD seedB = -phasePolarization seedD seedB ∧
    Matrix.trace (kmsModularWeight (2 : ℤ) (3 : ℤ) seedD seedB *
      movingPolePlus (3 : ℤ) (4 : ℤ) seedD seedB) = 9 * 9 + 4 * 16 := by
  decide

end ConcreteMatrixWitness

/-!
## 6. Diamond Causal Poset (`FiveStreamIntertwinerArchetype`) & Meta Epistemic Compiler
-/

section MetaEpistemicCompilerCertification

open InfoGeometry.MetaCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

/-- The 4-node diamond causal poset of the Five-Stream Master Intertwiner. -/
inductive FiveStreamIntertwinerArchetype where
  | crossStreamCarrierAndGrassmannianBridge
  | parabolicModularWeylRotorIntertwiner
  | kmsTraceAndJordanOscillatorIntertwiner
  | fiveStreamMasterSynthesisAndWitness
  deriving DecidableEq, Repr, Inhabited

namespace FiveStreamIntertwinerArchetype

private def equivFin : FiveStreamIntertwinerArchetype ≃ Fin 4 where
  toFun
    | .crossStreamCarrierAndGrassmannianBridge => 0
    | .parabolicModularWeylRotorIntertwiner => 1
    | .kmsTraceAndJordanOscillatorIntertwiner => 2
    | .fiveStreamMasterSynthesisAndWitness => 3
  invFun
    | 0 => .crossStreamCarrierAndGrassmannianBridge
    | 1 => .parabolicModularWeylRotorIntertwiner
    | 2 => .kmsTraceAndJordanOscillatorIntertwiner
    | _ => .fiveStreamMasterSynthesisAndWitness
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype FiveStreamIntertwinerArchetype :=
  Fintype.ofEquiv (Fin 4) equivFin.symm

def prerequisites : FiveStreamIntertwinerArchetype → Finset FiveStreamIntertwinerArchetype
  | .crossStreamCarrierAndGrassmannianBridge =>
      {.crossStreamCarrierAndGrassmannianBridge}
  | .parabolicModularWeylRotorIntertwiner =>
      {.crossStreamCarrierAndGrassmannianBridge, .parabolicModularWeylRotorIntertwiner}
  | .kmsTraceAndJordanOscillatorIntertwiner =>
      {.crossStreamCarrierAndGrassmannianBridge, .kmsTraceAndJordanOscillatorIntertwiner}
  | .fiveStreamMasterSynthesisAndWitness =>
      {.crossStreamCarrierAndGrassmannianBridge, .parabolicModularWeylRotorIntertwiner,
       .kmsTraceAndJordanOscillatorIntertwiner, .fiveStreamMasterSynthesisAndWitness}

instance instPartialOrder : PartialOrder FiveStreamIntertwinerArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE FiveStreamIntertwinerArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT FiveStreamIntertwinerArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

theorem weyl_and_kms_intertwiner_branches_incomparable :
    ¬ (parabolicModularWeylRotorIntertwiner ≤ kmsTraceAndJordanOscillatorIntertwiner) ∧
    ¬ (kmsTraceAndJordanOscillatorIntertwiner ≤ parabolicModularWeylRotorIntertwiner) := by
  decide

def canonicalPending : List FiveStreamIntertwinerArchetype :=
  [.fiveStreamMasterSynthesisAndWitness, .kmsTraceAndJordanOscillatorIntertwiner,
   .parabolicModularWeylRotorIntertwiner, .crossStreamCarrierAndGrassmannianBridge]

def canonicalSchedule : List FiveStreamIntertwinerArchetype :=
  [.crossStreamCarrierAndGrassmannianBridge, .kmsTraceAndJordanOscillatorIntertwiner,
   .parabolicModularWeylRotorIntertwiner, .fiveStreamMasterSynthesisAndWitness]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

theorem compile_canonicalPending :
    compile (∅ : Finset FiveStreamIntertwinerArchetype) canonicalPending =
      some canonicalSchedule := by
  decide

end FiveStreamIntertwinerArchetype

/-- Node 0 proved `TypedArchetype`: Stream 1 Grassmannian Peirce extraction of Stream 5 seeds. -/
def arch0CrossStreamCarrierAndGrassmannianBridge : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.FiveStreamMasterIntertwiner.arch0CrossStreamCarrierAndGrassmannianBridge
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    cotangentNilpotent (DeBruijnRotorAlternationCycle.polePlus seedD seedB) seedD = seedD ∧
    tangentNilpotent (DeBruijnRotorAlternationCycle.polePlus seedD seedB) seedB = seedB ∧
    normalBundlePart (DeBruijnRotorAlternationCycle.polePlus seedD seedB)
      (transitionVelocity seedD seedB) = 0
  evidence := fun _ =>
    grassmannian_peirce_extracts_seeds_and_horizontal_velocity mat2Z_isDualSeedPair

/-- Node 1 proved `TypedArchetype`: Stream 4 Parabolic/Bruhat Weyl unit intertwines Stream 5 rotor. -/
def arch1ParabolicModularWeylRotorIntertwiner : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.FiveStreamMasterIntertwiner.arch1ParabolicModularWeylRotorIntertwiner
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    phaseRotor (0 : ℤ) (1 : ℤ) seedD seedB = bruhatQuarticOp seedD seedB ∧
    bruhatQuarticOp seedD seedB * phasePolarization seedD seedB *
      bruhatQuarticOpInv seedD seedB = -phasePolarization seedD seedB ∧
    parabolicHexalityOp seedD seedB ^ 3 * wheelGenerator seedD seedB =
      -wheelGenerator seedD seedB
  evidence := fun _ =>
    ⟨(phaseRotor_quarter_turn_eq_bruhatQuarticOp mat2Z_isDualSeedPair).1,
     bruhatQuarticOp_reverses_phasePolarization mat2Z_isDualSeedPair,
     (modular_center_acts_as_minus_one_on_oscillator mat2Z_isDualSeedPair).2⟩

/-- Node 2 proved `TypedArchetype`: Stream 3 KMS tracial rotor interpolation & Jordan `[L_d, L_B]` swap. -/
def arch2KmsTraceAndJordanOscillatorIntertwiner : TypedArchetype (ℤ × ℤ) .proved where
  name := `InfoGeometry.Canonical.FiveStreamMasterIntertwiner.arch2KmsTraceAndJordanOscillatorIntertwiner
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    Matrix.trace (kmsModularWeight (2 : ℤ) (3 : ℤ) seedD seedB *
      movingPolePlus p.1 p.2 seedD seedB) =
      (9 * (p.1 * p.1)) * Matrix.trace (DeBruijnRotorAlternationCycle.polePlus seedD seedB) +
      (4 * (p.2 * p.2)) * Matrix.trace (DeBruijnRotorAlternationCycle.poleMinus seedD seedB) ∧
    (InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) seedD *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) seedB -
     InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) seedB *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) seedD)
      (transitionVelocity seedD seedB) = 2 • wheelGenerator seedD seedB
  evidence := fun p =>
    ⟨tracial_kms_movingPolePlus_interpolation mat2Z_isDualSeedPair
       (Matrix.traceLinearMap (Fin 2) ℤ ℤ) (fun x y => Matrix.trace_mul_comm x y) 2 3 p.1 p.2,
     (jordanLeft_commutator_intertwines_velocity_and_wheel mat2Z_isDualSeedPair).1⟩

/-- Node 3 proved `TypedArchetype`: Master 5-stream synthesis & concrete trace witness. -/
def arch3FiveStreamMasterSynthesisAndWitness : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.FiveStreamMasterIntertwiner.arch3FiveStreamMasterSynthesisAndWitness
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    seedD * seedB ≠ seedB * seedD ∧
    Matrix.trace (kmsModularWeight (2 : ℤ) (3 : ℤ) seedD seedB *
      movingPolePlus (3 : ℤ) (4 : ℤ) seedD seedB) = 9 * 9 + 4 * 16
  evidence := fun _ =>
    ⟨mat2Z_five_stream_intertwiner_witness.1,
     mat2Z_five_stream_intertwiner_witness.2.2.2.2.2.2⟩

#register_archetype arch0CrossStreamCarrierAndGrassmannianBridge
#register_archetype arch1ParabolicModularWeylRotorIntertwiner
#register_archetype arch2KmsTraceAndJordanOscillatorIntertwiner
#register_archetype arch3FiveStreamMasterSynthesisAndWitness

#audit_archetype arch0CrossStreamCarrierAndGrassmannianBridge
#audit_archetype arch1ParabolicModularWeylRotorIntertwiner
#audit_archetype arch2KmsTraceAndJordanOscillatorIntertwiner
#audit_archetype arch3FiveStreamMasterSynthesisAndWitness

def fiveStreamIntertwinerStatement : FiveStreamIntertwinerArchetype → Prop
  | .crossStreamCarrierAndGrassmannianBridge =>
      arch0CrossStreamCarrierAndGrassmannianBridge.claim ()
  | .parabolicModularWeylRotorIntertwiner =>
      arch1ParabolicModularWeylRotorIntertwiner.claim ()
  | .kmsTraceAndJordanOscillatorIntertwiner =>
      ∀ p : ℤ × ℤ, arch2KmsTraceAndJordanOscillatorIntertwiner.claim p
  | .fiveStreamMasterSynthesisAndWitness =>
      arch3FiveStreamMasterSynthesisAndWitness.claim ()

lemma fiveStreamIntertwinerRules : ProofRules fiveStreamIntertwinerStatement := by
  intro target _
  cases target with
  | crossStreamCarrierAndGrassmannianBridge =>
      exact arch0CrossStreamCarrierAndGrassmannianBridge.discharge ()
  | parabolicModularWeylRotorIntertwiner =>
      exact arch1ParabolicModularWeylRotorIntertwiner.discharge ()
  | kmsTraceAndJordanOscillatorIntertwiner =>
      exact fun p => arch2KmsTraceAndJordanOscillatorIntertwiner.discharge p
  | fiveStreamMasterSynthesisAndWitness =>
      exact arch3FiveStreamMasterSynthesisAndWitness.discharge ()

/-- Certified execution of the Meta Epistemic Compiler on the `FiveStreamIntertwinerArchetype` diamond poset. -/
theorem five_stream_intertwiner_executable_certified_compilation :
    ∃ schedule : List FiveStreamIntertwinerArchetype,
      compile ∅ FiveStreamIntertwinerArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card FiveStreamIntertwinerArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, fiveStreamIntertwinerStatement target :=
  executable_certified_compilation
    fiveStreamIntertwinerStatement
    fiveStreamIntertwinerRules
    FiveStreamIntertwinerArchetype.canonicalPending
    FiveStreamIntertwinerArchetype.canonicalPending_nodup
    FiveStreamIntertwinerArchetype.canonicalPending_univ

end MetaEpistemicCompilerCertification

end InfoGeometry.Canonical.FiveStreamMasterIntertwiner
