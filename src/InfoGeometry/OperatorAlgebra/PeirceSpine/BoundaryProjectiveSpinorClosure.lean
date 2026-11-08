/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.PolarDeWittIwasawa
import InfoGeometry.OperatorAlgebra.PeirceSpine.ProjectiveNullSpinor
import InfoGeometry.OperatorAlgebra.PeirceSpine.QuantumAffineFlagClusterPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.GeneratorDefect

/-!
# Native closure for the Peirce boundary, affine chord, spinor action, and nilpotent top mode

This module assembles ring identities from the existing Peirce owners. It does not identify an
arbitrary ring element with a geometric volume, define a GNS state, or assert an unconditional
projective-ray quotient. The proposed universal A₉₁ scaling statement is false without additional
commutation data; the conditional ordered identity below records exactly where that data enters.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- Boundary evaluation at the idempotent and the resulting mixed-cone volume/curvature laws. -/
theorem boundary_cone_evaluation_and_mixed_volume {P : B} (hP : P * P = P) (A C : B) :
    superDerivPlus P A P = -conePlus P A ∧
    superDerivMinus P C P = coneMinus P C ∧
    superDerivPlus P A (superDerivPlus P A P) = 0 ∧
    superDerivMinus P C (superDerivMinus P C P) = 0 ∧
    superDerivPlus P A (coneMinus P C) = genV P A C ∧
    superDerivMinus P C (conePlus P A) = genV P A C ∧
    superDerivPlusBar P A (coneMinus P C) = genSig P A C ∧
    superDerivMinusBar P C (conePlus P A) = -genSig P A C := by
  have hOwner := archetype_A28_graded_derivations hP A C P P
  rcases hOwner with ⟨_, _, _, _, _, _, _, _, _, _, _, hPlusV, hMinusV,
    hPlusBar, hMinusBar⟩
  refine ⟨?_, ?_, ?_, ?_, hPlusV, hMinusV, hPlusBar, hMinusBar⟩
  · simp only [superDerivPlus, conePlus, parityConj, invS]
    peirce_nf hP
  · simp only [superDerivMinus, coneMinus, parityConj, invS]
    peirce_nf hP
  · simp only [superDerivPlus, superDerivMinus, conePlus, coneMinus, parityConj, invS]
    peirce_nf hP
  · simp only [superDerivMinus, superDerivPlus, coneMinus, conePlus, parityConj, invS]
    peirce_nf hP

/-- A88's complete boundary/Stokes package, including the vanishing Cartan-Clifford
norms and the coboundary substitutions of `d₋ P = N₋`.  The norms are stated
through the existing polar owner; this theorem adds no geometric interpretation. -/
theorem archetype_A88_zero_volume_nilpotent_boundary_and_stokes_law
    {P : B} (hP : P * P = P) (A C : B) :
    PolarDeWittIwasawa.cliffordNorm P (conePlus P A) = 0 ∧
    PolarDeWittIwasawa.cliffordNorm P (coneMinus P C) = 0 ∧
    superDerivPlus P A P = -conePlus P A ∧
    superDerivMinus P C P = coneMinus P C ∧
    superDerivPlus P A (superDerivPlus P A P) = 0 ∧
    superDerivMinus P C (superDerivMinus P C P) = 0 ∧
    superDerivPlus P A (coneMinus P C) = genV P A C ∧
    superDerivMinus P C (conePlus P A) = genV P A C ∧
    superDerivPlus P A (superDerivMinus P C P) = genV P A C ∧
    superDerivPlusBar P A (superDerivMinus P C P) = genSig P A C := by
  have hN := archetype_A3_nilpotent_cones_and_tetraktys_table hP A C
  have hCartan := PolarDeWittIwasawa.archetype_A84_cartan_clifford_norm hP A C
  have hBoundary := boundary_cone_evaluation_and_mixed_volume hP A C
  rcases hBoundary with ⟨hPlusP, hMinusP, hPlusSq, hMinusSq, hVPlus, hVMinus,
    hSigPlus, _⟩
  refine ⟨?_, ?_, hPlusP, hMinusP, hPlusSq, hMinusSq, hVPlus, hVMinus, ?_, ?_⟩
  · dsimp [PolarDeWittIwasawa.cliffordNorm, PolarDeWittIwasawa.theta,
      PolarDeWittIwasawa.parity, PolarDeWittIwasawa.complement]
    have hTheta := hCartan.1
    have hNil := hN.1
    dsimp [PolarDeWittIwasawa.nPlus] at hTheta
    change conePlus P A * PolarDeWittIwasawa.theta P (conePlus P A) = 0
    rw [show PolarDeWittIwasawa.theta P (conePlus P A) = -conePlus P A by
      simpa [PolarDeWittIwasawa.nPlus, PolarDeWittIwasawa.complement,
        conePlus] using hCartan.1]
    calc
      conePlus P A * -conePlus P A =
          -(conePlus P A * conePlus P A) := by noncomm_ring
      _ = 0 := by rw [hN.1]; simp
  · dsimp [PolarDeWittIwasawa.cliffordNorm, PolarDeWittIwasawa.theta,
      PolarDeWittIwasawa.parity, PolarDeWittIwasawa.complement]
    have hTheta := hCartan.2.1
    have hNil := hN.2.1
    dsimp [PolarDeWittIwasawa.nMinus] at hTheta
    change coneMinus P C * PolarDeWittIwasawa.theta P (coneMinus P C) = 0
    rw [show PolarDeWittIwasawa.theta P (coneMinus P C) = -coneMinus P C by
      simpa [PolarDeWittIwasawa.nMinus, PolarDeWittIwasawa.complement,
        coneMinus] using hCartan.2.1]
    calc
      coneMinus P C * -coneMinus P C =
          -(coneMinus P C * coneMinus P C) := by noncomm_ring
      _ = 0 := by rw [hN.2.1]; simp
  · rw [hMinusP]; exact hVPlus
  · rw [hMinusP]; exact hSigPlus

/-- Corrected bulk reconstruction laws for an arbitrary operator input. The
second expression is right multiplication by `V`; it is not the crossed
corner transfer `N₊ X N₋ + N₋ X N₊` asserted in the source transcript. -/
theorem boundary_bulk_nested_bracket_readout {P : B} (hP : P * P = P)
    (A C X : B) :
    anticomm (genPhi P A C) (comm (genPhi P A C) X) =
      comm (genV P A C) X ∧
    anticomm (genV P A C) X -
        comm (genPhi P A C) (anticomm (genPhi P A C) X) =
      (2 : ℤ) • (X * genV P A C) := by
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
  constructor
  · simp only [anticomm, comm]
    rw [← hPhiSq]
    noncomm_ring
  · exact tetraktys_nested_bulk_expression hP A C X

/-- The two unipotently transported idempotents have squared cross-chord `V`.
This is an algebraic identity; no metric or projective-boundary interpretation is assumed. -/
theorem affine_chart_cross_chord_square {P : B} (hP : P * P = P) (A C : B) :
    (conjPlus P A P - conjMinus P C P) * (conjPlus P A P - conjMinus P C P) =
      genV P A C ∧
    1 - (conjPlus P A P - conjMinus P C P) * (conjPlus P A P - conjMinus P C P) =
      1 - genV P A C ∧
    (invS P + genJ P A C) * (invS P + genJ P A C) = 1 - genV P A C ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = 1 + genV P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [conjPlus, conjMinus]
    peirce_nf hP
  · simp only [conjPlus, conjMinus]
    peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- A89's affine-chart and Nambu-factor identities, expressed with the existing
Peirce chart displacement and Bergman operator. The factor `1 - V` is an
operator identity; no boundary quotient or geometric compactification is
asserted. -/
theorem archetype_A89_affine_chart_nambu_factor_identities
    {P : B} (hP : P * P = P) (A C : B) :
    PolarDeWittIwasawa.cliffordNorm P
        (P - (P - conePlus P A)) = 0 ∧
    PolarDeWittIwasawa.cliffordNorm P
        ((1 - P) - ((1 - P) - coneMinus P C)) = 0 ∧
    bergmanOp P A C 1 = 1 - genV P A C ∧
    evenGrade P (PolarDeWittIwasawa.cliffordNorm P
        (invS P + genPhi P A C)) = bergmanOp P A C 1 ∧
    (invS P + genJ P A C) * (invS P + genJ P A C) =
      bergmanOp P A C 1 ∧
    PolarDeWittIwasawa.cliffordNorm P (invS P + genJ P A C) =
      1 + genV P A C - (2 : ℤ) • genPhi P A C := by
  refine ⟨?_, ?_, (archetype_A23_bergman_operator hP A C).1, ?_, ?_, ?_⟩
  · dsimp [PolarDeWittIwasawa.cliffordNorm, PolarDeWittIwasawa.theta,
      PolarDeWittIwasawa.parity, PolarDeWittIwasawa.complement]
    peirce_nf hP
  · dsimp [PolarDeWittIwasawa.cliffordNorm, PolarDeWittIwasawa.theta,
      PolarDeWittIwasawa.parity, PolarDeWittIwasawa.complement]
    peirce_nf hP
  · dsimp [PolarDeWittIwasawa.cliffordNorm, PolarDeWittIwasawa.theta,
      PolarDeWittIwasawa.parity, PolarDeWittIwasawa.complement, evenGrade]
    peirce_nf hP
    rw [(archetype_A23_bergman_operator hP A C).1]
    simp only [genV, anticomm]
    abel
  · calc
      (invS P + genJ P A C) * (invS P + genJ P A C) =
          1 - genV P A C := (affine_chart_cross_chord_square hP A C).2.2.1
      _ = bergmanOp P A C 1 := (archetype_A23_bergman_operator hP A C).1.symm
  · dsimp [PolarDeWittIwasawa.cliffordNorm,
      PolarDeWittIwasawa.theta, PolarDeWittIwasawa.parity,
      PolarDeWittIwasawa.complement]
    peirce_nf hP

/-- Exact rescaled-sandwich factorization, conditional on the commutation needed to move the
right scale across the unscaled left-observable product. No division or quotient is used. -/
theorem ordered_sandwich_scale_factorization
    {N M X leftScale rightScale : B}
    (hScale : (N * X) * rightScale = rightScale * (N * X)) :
    (leftScale * N) * X * (rightScale * M) =
      (leftScale * rightScale) * (N * X * M) := by
  calc
    (leftScale * N) * X * (rightScale * M) =
        leftScale * ((N * X) * rightScale) * M := by noncomm_ring
    _ = leftScale * (rightScale * (N * X)) * M := by rw [hScale]
    _ = (leftScale * rightScale) * (N * X * M) := by noncomm_ring

/-- The A91 unnormalized sandwich of an arbitrary observable. -/
def boundaryGnsExpectation (P A C X : B) : B :=
  conePlus P A * X * coneMinus P C

/-- The ordered two-sided Peirce rescaling used in the A91 source. -/
def boundaryGnsExpectationScaled (P A C leftScale rightScale X : B) : B :=
  (leftScale * conePlus P A) * X * (rightScale * coneMinus P C)

/-- Exact obstruction to the source's unconditional homogeneous scaling law.
The discrepancy is the observable commutator with the operator-valued metric;
it vanishes, for example, under the explicit condition `[X, V] = 0`. -/
theorem archetype_A91_scaled_sandwich_commutator_residual
    {P : B} (hP : P * P = P) (A C X : B) :
    boundaryGnsExpectationScaled P A C
        (genV P A C - 1) (genV P A C + 1) X -
      ((genV P A C * genV P A C - 1) *
        boundaryGnsExpectation P A C X) =
      (genV P A C - 1) * conePlus P A *
        comm X (genV P A C) * coneMinus P C := by
  simp only [boundaryGnsExpectationScaled, boundaryGnsExpectation, comm]
  peirce_nf hP

/-- The internal two-state action of `N₊`, `N₋`, `Φ`, `J`, and `Σ` on
`(N₊, Q₋)`, including the operator-valued return coefficient `V`. -/
theorem internal_two_state_spinor_action {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * P = 0 ∧
    qgtMinus P A C * P = 0 ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * conePlus P A = qgtMinus P A C ∧
    coneMinus P C * qgtMinus P A C = 0 ∧
    conePlus P A * qgtMinus P A C = genV P A C * conePlus P A ∧
    genPhi P A C * conePlus P A = qgtMinus P A C ∧
    genPhi P A C * qgtMinus P A C = genV P A C * conePlus P A ∧
    genJ P A C * conePlus P A = -qgtMinus P A C ∧
    genJ P A C * qgtMinus P A C = genV P A C * conePlus P A ∧
    genSig P A C * conePlus P A = genV P A C * conePlus P A ∧
    genSig P A C * qgtMinus P A C = -(genV P A C * qgtMinus P A C) := by
  refine ⟨conePlus_mul_P hP A, qgtMinus_mul_P hP A C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · rfl
  · exact coneMinus_mul_qgtMinus hP A C
  · exact conePlus_mul_qgtMinus hP A C
  · exact genPhi_mul_conePlus hP A C
  · exact genPhi_mul_qgtMinus hP A C
  · exact genJ_mul_conePlus hP A C
  · exact genJ_mul_qgtMinus hP A C
  · exact genSig_mul_conePlus hP A C
  · exact genSig_mul_qgtMinus hP A C

/-- The two ordered unipotent factors used for the source transcript's
two-sided Bruhat conjugation. -/
def boundaryBruhatFactor (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C)

def boundaryBruhatFactorInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A)

def boundaryBruhatState (P A C : B) : B :=
  boundaryBruhatFactor P A C * P * boundaryBruhatFactorInv P A C

def boundaryBruhatConjugate (P A C X : B) : B :=
  boundaryBruhatFactor P A C * X * boundaryBruhatFactorInv P A C

def boundaryBruhatReduced11 (P A C : B) : B :=
  P * boundaryBruhatState P A C * P

def boundaryBruhatReduced00 (P A C : B) : B :=
  (1 - P) * boundaryBruhatState P A C * (1 - P)

/-- A95's exact ring content: the Bruhat conjugate is idempotent; its two
diagonal Peirce compressions are `P - Q₊` and `Q₋`; their signed readouts
recover `V` and `Σ`, and their summed idempotency defects recover `δ(V)`. -/
theorem boundary_bruhat_reduced_state_readout {P : B} (hP : P * P = P)
    (A C : B) :
    boundaryBruhatState P A C * boundaryBruhatState P A C =
      boundaryBruhatState P A C ∧
    boundaryBruhatReduced11 P A C = P - qgtPlus P A C ∧
    boundaryBruhatReduced00 P A C = qgtMinus P A C ∧
    (P - boundaryBruhatReduced11 P A C) +
        boundaryBruhatReduced00 P A C = genV P A C ∧
    (P - boundaryBruhatReduced11 P A C) -
        boundaryBruhatReduced00 P A C = genSig P A C ∧
    idempotencyDefect (boundaryBruhatReduced11 P A C) =
      idempotencyDefect (qgtPlus P A C) ∧
    idempotencyDefect (boundaryBruhatReduced00 P A C) =
      idempotencyDefect (qgtMinus P A C) ∧
    idempotencyDefect (boundaryBruhatReduced11 P A C) +
        idempotencyDefect (boundaryBruhatReduced00 P A C) =
      idempotencyDefect (genV P A C) := by
  simp only [boundaryBruhatState, boundaryBruhatFactor,
    boundaryBruhatFactorInv, boundaryBruhatReduced11,
    boundaryBruhatReduced00, idempotencyDefect, qgtPlus, qgtMinus]
  peirce_nf hP
  trivial

/-- A96's algebraic protection contract: the metric, its complement, and its
idempotency defect are fixed by the ordered Bruhat conjugation. The `hProjV`
channel rejects the displayed single-link shears of the Tetraktys modes. -/
theorem boundary_bulk_error_filter {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A (genV P A C) = genV P A C ∧
    conjMinus P C (genV P A C) = genV P A C ∧
    boundaryBruhatConjugate P A C (genV P A C) = genV P A C ∧
    boundaryBruhatConjugate P A C (1 - genV P A C) = 1 - genV P A C ∧
    boundaryBruhatConjugate P A C (idempotencyDefect (genV P A C)) =
      idempotencyDefect (genV P A C) ∧
    hProjV P A C (conjPlus P A (genV P A C)) =
      hProjV P A C (genV P A C) ∧
    hProjV P A C (conjMinus P C (genV P A C)) =
      hProjV P A C (genV P A C) ∧
    hProjV P A C (conjPlus P A (genPhi P A C)) = 0 ∧
    hProjV P A C (conjPlus P A (genJ P A C)) = 0 ∧
    hProjV P A C (conjPlus P A (genSig P A C)) = 0 ∧
    hProjV P A C (conjMinus P C (genPhi P A C)) = 0 ∧
    hProjV P A C (conjMinus P C (genJ P A C)) = 0 ∧
    hProjV P A C (conjMinus P C (genSig P A C)) = 0 := by
  simp only [boundaryBruhatConjugate, boundaryBruhatFactor,
    boundaryBruhatFactorInv, conjPlus, conjMinus, hProjV,
    derivSqPhi, derivSqJ, derivSqSig, idempotencyDefect]
  peirce_nf hP
  trivial

/-- Source-order A97: the transcript's primal and dual exponential families
are the unipotent Peirce units `1 + N₊` and `1 + N₋`. This theorem records
their additive group laws, the ordered cross-sheet cumulants, and the
operator-valued metric/skew readouts without adding an exponential alias. -/
theorem archetype_A97_unipotent_families_and_two_sheeted_cumulant_laws
    {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ : B) :
    (1 + conePlus P A₁) * (1 + conePlus P A₂) =
      1 + conePlus P (A₁ + A₂) ∧
    (1 + conePlus P A) * (1 - conePlus P A) = 1 ∧
    (1 + coneMinus P C₁) * (1 + coneMinus P C₂) =
      1 + coneMinus P (C₁ + C₂) ∧
    (1 + coneMinus P C) * (1 - coneMinus P C) = 1 ∧
    comm (1 + conePlus P A) (1 + coneMinus P C) = genSig P A C ∧
    anticomm (1 + conePlus P A) (1 + coneMinus P C) =
      (2 : ℤ) • (1 + genPhi P A C) + genV P A C ∧
    ((P + coneMinus P C) - (P - conePlus P A)) *
        ((P + coneMinus P C) - (P - conePlus P A)) = genV P A C ∧
    comm (P - (P - conePlus P A)) ((P + coneMinus P C) - P) =
      genSig P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C := by
  simp only [conePlus, coneMinus, qgtPlus, qgtMinus, genPhi, genV,
    genSig, anticomm, comm]
  peirce_nf hP
  trivial

/-- A nilpotent top mode is annihilated on both sides and is therefore a zero-mode for
both the commutator and anticommutator with its generator. -/
theorem nilpotent_top_mode_zero_modes {n : ℕ} (X : B)
    (hNil : opPow (n + 1) X = 0) :
    opPow n X * X = 0 ∧
    X * opPow n X = 0 ∧
    comm X (opPow n X) = 0 ∧
    anticomm X (opPow n X) = 0 := by
  obtain ⟨hXpow, hPowX⟩ := nilpotent_predecessor_power_annihilated n X hNil
  refine ⟨hPowX, hXpow, ?_, ?_⟩
  · unfold comm
    rw [hXpow, hPowX, sub_self]
  · unfold anticomm
    rw [hXpow, hPowX, add_zero]

/-- A92's chiral harmonic identities together with the general nilpotent
top-power zero-mode law. The four chiral-prime equations are algebraic
self/anti-duality identities in the two Peirce corners. -/
theorem archetype_A92_chiral_harmonic_and_parafermion_boundary_zero_modes
    {P : B} (hP : P * P = P) (A C N : B) (k : ℕ) :
    superDerivPlus P A (conePlus P A) = 0 ∧
    superDerivPlusBar P A (conePlus P A) = 0 ∧
    superDerivMinus P C (coneMinus P C) = 0 ∧
    superDerivMinusBar P C (coneMinus P C) = 0 ∧
    superDerivPlus P A (qgtPlus P A C) +
      superDerivPlusBar P A (qgtPlus P A C) = 0 ∧
    superDerivMinus P C (qgtMinus P A C) +
      superDerivMinusBar P C (qgtMinus P A C) = 0 ∧
    superDerivPlus P A (qgtMinus P A C) -
      superDerivPlusBar P A (qgtMinus P A C) = 0 ∧
    superDerivMinus P C (qgtPlus P A C) -
      superDerivMinusBar P C (qgtPlus P A C) = 0 ∧
    (opPow (k + 1) N = 0 →
      opPow k N * N = 0 ∧ N * opPow k N = 0 ∧
      comm N (opPow k N) = 0 ∧ anticomm N (opPow k N) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hNil =>
    nilpotent_top_mode_zero_modes (n := k) N hNil⟩
  all_goals first
    | peirce_nf hP
    | (simp only [superDerivPlus, superDerivMinus, superDerivPlusBar,
        superDerivMinusBar, parityConj, invS, qgtPlus, qgtMinus,
        genPhi, genV, genSig, conePlus, coneMinus]; peirce_nf hP)

/-- A94's source-facing finite-ring content. The left-only Laplacian and its
left-only Hodge dual from the source are corrected to the exact two-sided
operator formulas. The defect mismatch and its `V`-compensated cancellation
remain exact Peirce identities; no geometric anomaly interpretation is used. -/
theorem archetype_A94_corrected_radial_laplacian_and_defect_cancellation
    {P : B} (hP : P * P = P) (A C X : B) :
    hodgeLaplacianPhi P A C X =
      (2 : ℤ) • (genV P A C * X + X * genV P A C) ∧
    hodgeStar P (hodgeLaplacianPhi P A C X) =
      (2 : ℤ) • (genSig P A C * X + invS P * X * genV P A C) ∧
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      -((4 : ℤ) •
        (idempotencyDefect (genV P A C) * genPhi P A C)) ∧
    derivSqSig P A C (genJ P A C) - derivSqPhi P A C (genJ P A C) =
      -((4 : ℤ) •
        (idempotencyDefect (genV P A C) * genJ P A C)) ∧
    derivSqSig P A C (genPhi P A C) -
        genV P A C * derivSqJ P A C (genPhi P A C) = 0 ∧
    derivSqSig P A C (genJ P A C) -
        genV P A C * derivSqPhi P A C (genJ P A C) = 0 := by
  refine ⟨hodgeLaplacianPhi_eq hP A C X,
    hodgeStar_hodgeLaplacianPhi hP A C X,
    defect_deriv_sig_sub_j hP A C,
    defect_deriv_sig_sub_phi hP A C, ?_, ?_⟩
  · simp only [derivSqSig, derivSqJ]
    peirce_nf hP
  · simp only [derivSqSig, derivSqPhi]
    peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
