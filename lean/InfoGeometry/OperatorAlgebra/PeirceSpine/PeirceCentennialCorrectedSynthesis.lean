/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.BoundaryProjectiveSpinorClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorBogoliubovSpinePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis

/-!
# Corrected source-order A100 synthesis

This is the source-facing finite-ring synthesis of the shared-link A100
packet. It reuses the Peirce, homogenization, corrected Hodge, Bruhat, and
modular owners. Two source claims are stated in their valid forms: the Hodge
Jordan Laplacian has both left and right `V` actions, and the mixed graded
anticommutator is `{V, X}`, not the modular derivation `[Σ, X]`. No analytic
exponential, state, or KMS condition is introduced.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open PeirceExponentialModularSynthesis

variable {B : Type*} [Ring B]

/-- Quadratic idempotency defect used in the source A100 square-root laws. -/
def centennialDefect (X : B) : B := X * X - X

/-- The source A100 master packet, with its two noncommutative corrections
made explicit. Every item is an arbitrary-ring identity for a Peirce cut. -/
theorem archetype_A100_corrected_centennial_master
    {P : B} (hP : P * P = P) (A C X : B) :
    -- Tetraktys and orthogonal channel products.
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    qgtPlus P A C * qgtMinus P A C = 0 ∧
    -- Homogenized channel resolution and Fourier agreement on the metric.
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genV P A C) = fourierV P A C (genV P A C) ∧
    -- Affine chart chord and its exact squared metric.
    conjMinus P C P - conjPlus P A P = genPhi P A C ∧
    (conjMinus P C P - conjPlus P A P) *
        (conjMinus P C P - conjPlus P A P) = genV P A C ∧
    comm (P - conjPlus P A P) (conjMinus P C P - P) = genSig P A C ∧
    -- Flatness of the two ordered connection actions.
    connPlus P A C (connMinus P A C X) =
      connMinus P A C (connPlus P A C X) ∧
    -- Hodge duality and the corrected two-sided Jordan Laplacian.
    superDerivPhiBar P A C X =
      -hodgeStar P (superDerivPhi P A C (hodgeStar P X)) ∧
    hodgeLaplacianPhi P A C X =
      (2 : ℤ) • (genV P A C * X + X * genV P A C) ∧
    -- Defect tower and Nambu square.
    (genSig P A C + genJ P A C) * (genSig P A C + genJ P A C) =
      centennialDefect (genV P A C) ∧
    centennialDefect (-genPhi P A C) * centennialDefect (genPhi P A C) =
      centennialDefect (genV P A C) ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) =
      (1 + qgtPlus P A C) * (1 + qgtMinus P A C) ∧
    -- Bruhat reduced-state metric and defect recovery.
    (P - boundaryBruhatReduced11 P A C) + boundaryBruhatReduced00 P A C =
      genV P A C ∧
    centennialDefect (boundaryBruhatReduced11 P A C) +
        centennialDefect (boundaryBruhatReduced00 P A C) =
      centennialDefect (genV P A C) ∧
    -- Forward loxodromic rays and modular-time/phase actions.
    sigmaSandwichPlus P A C (conePlus P A) =
      ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A ∧
    sigmaSandwichPlus P A C (coneMinus P C) =
      ((1 - genV P A C) * (1 - genV P A C)) * coneMinus P C ∧
    modularTimeDeriv P A C (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    genJ P A C * (conePlus P A * X * coneMinus P C) * (-genJ P A C) =
      qgtMinus P A C * X * qgtMinus P A C ∧
    -- Corrected mixed graded term: it is Jordan multiplication by V.
    superDerivPlus P A (superDerivMinusBar P C X) +
        superDerivMinusBar P C (superDerivPlus P A X) =
      anticomm (genV P A C) X := by
  have hHom := archetype_A13_homogenized_projectors hP A C X
  have hFourier := archetype_A17_group_sandwich_character_table hP A C
  have hHodge := archetype_A34_hodge_conjugate_codifferentials hP A C X
  have hLap := hodgeLaplacianPhi_eq hP A C X
  have hBruhat := boundary_bruhat_reduced_state_readout hP A C
  have hLox := archetype_A98_loxodromic_sigma_sandwich_and_bruhat_actions hP A C X
  have hMod := archetype_A99_modular_time_and_phase_correlation_exchange hP A C X
  rcases hFourier with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hFourierV, _, _, _⟩
  rcases hBruhat with ⟨_, _, _, hMetric, _, _, _, hDefect⟩
  rcases hLox with ⟨_, _, hLoxPlus, hLoxMinus, _, _, _, _, _, _, _, _, _⟩
  rcases hMod with ⟨_, hMixed, _, hModPlus, _, _, _, _, _, hPhase, _, _, _⟩
  refine ⟨?_, ?_, ?_, hHom.1, hFourierV, ?_, ?_, ?_, ?_,
    hHodge.2.2.1, hLap,
    ?_, ?_, ?_, hMetric,
    (by simpa [centennialDefect,
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect] using hDefect),
    hLoxPlus, hLoxMinus, hModPlus, hPhase, hMixed⟩
  · simp only [genPhi, genV, anticomm, conePlus, coneMinus]
    peirce_nf hP
  · simp only [genJ, genV, anticomm, conePlus, coneMinus]
    peirce_nf hP
  · simp only [qgtPlus, qgtMinus, conePlus, coneMinus]
    peirce_nf hP
  · simp only [conjPlus, conjMinus]
    peirce_nf hP
  · simp only [conjPlus, conjMinus]
    peirce_nf hP
  · simp only [conjPlus, conjMinus, comm, genSig, qgtPlus, qgtMinus,
      conePlus, coneMinus]
    peirce_nf hP
  · simp only [connPlus, connMinus, qgtPlus, qgtMinus, comm,
      conePlus, coneMinus]
    peirce_nf hP
  · simp only [centennialDefect, genV, anticomm, genSig, comm,
      genJ, conePlus, coneMinus]
    peirce_nf hP
  · simp only [centennialDefect, genV, anticomm, genPhi,
      qgtPlus, qgtMinus, conePlus, coneMinus]
    peirce_nf hP
  · simp only [invS, genPhi, genV, anticomm, conePlus, coneMinus,
      qgtPlus, qgtMinus]
    peirce_nf hP
end InfoGeometry.OperatorAlgebra.PeirceSpine
