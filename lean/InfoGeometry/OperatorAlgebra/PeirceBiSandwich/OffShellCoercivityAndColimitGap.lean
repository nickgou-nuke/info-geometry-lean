/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Off-Shell Coercivity, Klein Reynolds Pinching, Daughter Defects & Colimit Gap Non-Commutation

Formalizes Archetype 5 (`Posets F₄..F₉, G₇..G₈`):
1. Integer scale-4 Klein Reynolds projector `kleinReynolds4` and scale-8 factored
   projector `factoredReynolds8` (valid over every associative ring without inverting `4`),
   together with eigenblock annihilation on non-invariant sectors.
2. Hermitian corner faithfulness (`[P, H] ≠ 0 ↔ N₊ ≠ 0 ↔ V ≠ 0`) vs. explicit
   `Mat₂(ℤ)` asymmetric nilpotent corner blindness (`N₊ = 0, [P, A] ≠ 0, V = 0`).
3. Oblique unipotent daughter conjugation signs (`P ± N₊`), non-Hermitian defect,
   Hermitian Gram defect `δ(P' (P')*) = Q₊² + Q₊`, square-root-free unitary Cayley
   cocycle `u_J = (1 - V + 2J)(1 + V)⁻¹`, and non-scalar `Mat₄(ℝ)` witness
   (`V = diag(1, 4, 1, 4)` non-central in `Mat₄(ℝ)`).
4. Support-projected operator coercivity factorization `V² - m² V = V(V - m² Π_V)` and
   `Mat₃(ℝ)` refutation of the scalar gap dichotomy (`V = diag(2, 3, 0)` non-scalar on
   its support `Π_V = diag(1, 1, 0)` with nontrivial kernel `1 - Π_V ≠ 0`).
5. Non-commutation of spectral mass gaps with inductive shell colimits, proved both at
   the scalar shell level (`v_k = 1 / (k + 1)`) and at the operator-tower level via
   compatible `Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ` shells (`V_shell n` strictly
   positive definite with gap `1 / (n + 1)` at every finite stage `n`, yet no uniform
   mass gap `m > 0` across the colimit).
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-! ### 1. Scale-4 Klein Reynolds & Scale-8 Factored Projectors (`G₇..G₈`) -/

/-- Scale-4 Klein Reynolds averaging operator over any associative ring. -/
def kleinReynolds4 {B : Type*} [Ring B] (P A C X : B) : B :=
  let V := casimirV P A C
  let Φ := phiOp P A C
  let J := jOp P A C
  let sigma := sigmaOp P A C
  V ^ 2 * X + V * (Φ * X * Φ - J * X * J) + sigma * X * sigma

/-- Bogus scale-5 perturbation illustrating failure to project off-diagonal modes. -/
def bogusReynolds {B : Type*} [Ring B] (P A C X : B) : B :=
  kleinReynolds4 P A C X + casimirV P A C ^ 2 * X

/-- Diagonal `ℤ/2` Klein pinch `X ↦ X + (2P - 1) X (2P - 1)`. -/
def diagPinch2 {B : Type*} [Ring B] (P X : B) : B :=
  X + (2 * P - 1) * X * (2 * P - 1)

/-- Factored scale-8 Klein Reynolds operator `Π⁽⁸⁾ = Π_Klein⁽⁴⁾ ∘ Π_diag⁽²⁾`. -/
def factoredReynolds8 {B : Type*} [Ring B] (P A C X : B) : B :=
  kleinReynolds4 P A C (diagPinch2 P X)

/-- Abstract commuting-involution Reynolds averaging operator `R_{S,T}(X) = X + SXS + TXT + STXTS`. -/
def involutionReynolds4 {B : Type*} [Ring B] (S T X : B) : B :=
  X + S * X * S + T * X * T + (S * T) * X * (T * S)

lemma comm_V_P {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    casimirV P A C * P = P * casimirV P A C := by
  rw [V_mul_P hP, P_mul_V hP]

lemma phiOp_sq {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    phiOp P A C * phiOp P A C = casimirV P A C := by
  dsimp [phiOp, casimirV, Qplus, Qminus]
  calc (Nplus P A + Nminus P C) * (Nplus P A + Nminus P C)
      = Nplus P A * Nplus P A + (Nplus P A * Nminus P C + Nminus P C * Nplus P A) +
        Nminus P C * Nminus P C := by noncomm_ring
    _ = Nplus P A * Nminus P C + Nminus P C * Nplus P A := by
        rw [Nplus_sq hP, Nminus_sq hP]; abel

lemma jOp_sq {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    jOp P A C * jOp P A C = -casimirV P A C := by
  dsimp [jOp, casimirV, Qplus, Qminus]
  calc (Nplus P A - Nminus P C) * (Nplus P A - Nminus P C)
      = Nplus P A * Nplus P A - (Nplus P A * Nminus P C + Nminus P C * Nplus P A) +
        Nminus P C * Nminus P C := by noncomm_ring
    _ = -(Nplus P A * Nminus P C + Nminus P C * Nplus P A) := by
        rw [Nplus_sq hP, Nminus_sq hP]; abel

lemma sigmaOp_sq {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    sigmaOp P A C * sigmaOp P A C = casimirV P A C ^ 2 := by
  dsimp [sigmaOp, casimirV]
  calc (Qplus P A C - Qminus P A C) * (Qplus P A C - Qminus P A C)
      = (Qplus P A C + Qminus P A C) ^ 2 -
        2 * (Qplus P A C * Qminus P A C + Qminus P A C * Qplus P A C) := by noncomm_ring
    _ = (Qplus P A C + Qminus P A C) ^ 2 := by
        rw [Qplus_mul_Qminus hP, Qminus_mul_Qplus hP]; noncomm_ring

/-- Scale-4 Klein Reynolds evaluation on all Peirce generators `{1, P, N₊, N₋, Φ, V}`,
    contrasted with the unclosed `bogusReynolds` perturbation. -/
theorem kleinReynolds4_on_generators {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    kleinReynolds4 P A C 1 = 4 * casimirV P A C ^ 2 ∧
    kleinReynolds4 P A C P = 2 * casimirV P A C ^ 2 ∧
    kleinReynolds4 P A C (Nplus P A) = 0 ∧
    kleinReynolds4 P A C (Nminus P C) = 0 ∧
    kleinReynolds4 P A C (phiOp P A C) = 0 ∧
    kleinReynolds4 P A C (casimirV P A C) = 4 * casimirV P A C ^ 3 ∧
    bogusReynolds P A C (casimirV P A C) = 5 * casimirV P A C ^ 3 ∧
    bogusReynolds P A C (phiOp P A C) = casimirV P A C ^ 2 * phiOp P A C := by
  have h1 : kleinReynolds4 P A C 1 = 4 * casimirV P A C ^ 2 := by
    dsimp [kleinReynolds4]
    calc casimirV P A C ^ 2 * 1 +
           casimirV P A C * (phiOp P A C * 1 * phiOp P A C - jOp P A C * 1 * jOp P A C) +
           sigmaOp P A C * 1 * sigmaOp P A C
        = casimirV P A C ^ 2 +
          casimirV P A C * (phiOp P A C * phiOp P A C - jOp P A C * jOp P A C) +
          sigmaOp P A C * sigmaOp P A C := by noncomm_ring
      _ = casimirV P A C ^ 2 + casimirV P A C * (casimirV P A C - (-casimirV P A C)) +
          casimirV P A C ^ 2 := by rw [phiOp_sq hP, jOp_sq hP, sigmaOp_sq hP]
      _ = 4 * casimirV P A C ^ 2 := by noncomm_ring
  have hP_eval : kleinReynolds4 P A C P = 2 * casimirV P A C ^ 2 := by
    have hPhiP : phiOp P A C * P * phiOp P A C = Qminus P A C := by
      dsimp [phiOp, Qminus]
      calc (Nplus P A + Nminus P C) * P * (Nplus P A + Nminus P C)
          = (Nplus P A * P + Nminus P C * P) * (Nplus P A + Nminus P C) := by noncomm_ring
        _ = Nminus P C * Nplus P A + Nminus P C * Nminus P C := by
            rw [Nplus_mul_P hP, Nminus_mul_P hP]; noncomm_ring
        _ = Nminus P C * Nplus P A := by rw [Nminus_sq hP]; abel
    have hJP : jOp P A C * P * jOp P A C = -Qminus P A C := by
      dsimp [jOp, Qminus]
      calc (Nplus P A - Nminus P C) * P * (Nplus P A - Nminus P C)
          = (Nplus P A * P - Nminus P C * P) * (Nplus P A - Nminus P C) := by noncomm_ring
        _ = -(Nminus P C * Nplus P A) + Nminus P C * Nminus P C := by
            rw [Nplus_mul_P hP, Nminus_mul_P hP]; noncomm_ring
        _ = -(Nminus P C * Nplus P A) := by rw [Nminus_sq hP]; abel
    have hSigP : sigmaOp P A C * P * sigmaOp P A C = Qplus P A C * Qplus P A C := by
      have hL : sigmaOp P A C * P = Qplus P A C := by
        dsimp [sigmaOp, Qplus, Qminus]
        calc (Nplus P A * Nminus P C - Nminus P C * Nplus P A) * P
            = Nplus P A * (Nminus P C * P) - Nminus P C * (Nplus P A * P) := by noncomm_ring
          _ = Nplus P A * Nminus P C := by rw [Nminus_mul_P hP, Nplus_mul_P hP]; noncomm_ring
      rw [hL]; dsimp [sigmaOp]
      calc Qplus P A C * (Qplus P A C - Qminus P A C)
          = Qplus P A C * Qplus P A C - Qplus P A C * Qminus P A C := by noncomm_ring
        _ = Qplus P A C * Qplus P A C := by rw [Qplus_mul_Qminus hP]; noncomm_ring
    have hV2P : casimirV P A C ^ 2 * P = Qplus P A C * Qplus P A C := by
      calc casimirV P A C ^ 2 * P
          = casimirV P A C * (casimirV P A C * P) := by noncomm_ring
        _ = (Qplus P A C + Qminus P A C) * Qplus P A C := by rw [V_mul_P hP]; rfl
        _ = Qplus P A C * Qplus P A C + Qminus P A C * Qplus P A C := by noncomm_ring
        _ = Qplus P A C * Qplus P A C := by rw [Qminus_mul_Qplus hP]; abel
    have hV2 : casimirV P A C ^ 2 = Qplus P A C * Qplus P A C + Qminus P A C * Qminus P A C := by
      dsimp [casimirV]
      calc (Qplus P A C + Qminus P A C) ^ 2
          = Qplus P A C * Qplus P A C + Qminus P A C * Qminus P A C +
            (Qplus P A C * Qminus P A C + Qminus P A C * Qplus P A C) := by noncomm_ring
        _ = Qplus P A C * Qplus P A C + Qminus P A C * Qminus P A C := by
            rw [Qplus_mul_Qminus hP, Qminus_mul_Qplus hP]; abel
    dsimp [kleinReynolds4]
    rw [hV2P, hPhiP, hJP, hSigP, hV2]
    dsimp [casimirV]
    calc Qplus P A C * Qplus P A C +
           (Qplus P A C + Qminus P A C) * (Qminus P A C - -Qminus P A C) +
           Qplus P A C * Qplus P A C
        = 2 * (Qplus P A C * Qplus P A C + Qminus P A C * Qminus P A C) +
          2 * (Qplus P A C * Qminus P A C) := by noncomm_ring
      _ = 2 * (Qplus P A C * Qplus P A C + Qminus P A C * Qminus P A C) := by
          rw [Qplus_mul_Qminus hP]; noncomm_ring
  have hNp : kleinReynolds4 P A C (Nplus P A) = 0 := by
    have hmid : phiOp P A C * Nplus P A * phiOp P A C - jOp P A C * Nplus P A * jOp P A C = 0 := by
      dsimp [phiOp, jOp]
      calc (Nplus P A + Nminus P C) * Nplus P A * (Nplus P A + Nminus P C) -
             (Nplus P A - Nminus P C) * Nplus P A * (Nplus P A - Nminus P C)
          = 2 * ((Nplus P A * Nplus P A) * Nminus P C + Nminus P C * (Nplus P A * Nplus P A)) := by
            noncomm_ring
        _ = 0 := by rw [Nplus_sq hP]; noncomm_ring
    have hSigL : sigmaOp P A C * Nplus P A = casimirV P A C * Nplus P A := by
      dsimp [sigmaOp, casimirV, Qplus, Qminus]
      calc (Nplus P A * Nminus P C - Nminus P C * Nplus P A) * Nplus P A
          = (Nplus P A * Nminus P C + Nminus P C * Nplus P A) * Nplus P A -
            2 * Nminus P C * (Nplus P A * Nplus P A) := by noncomm_ring
        _ = (Nplus P A * Nminus P C + Nminus P C * Nplus P A) * Nplus P A := by
            rw [Nplus_sq hP]; noncomm_ring
    have hNpSig : Nplus P A * sigmaOp P A C = -(casimirV P A C * Nplus P A) := by
      rw [V_comm_Nplus hP]
      dsimp [sigmaOp, casimirV, Qplus, Qminus]
      calc Nplus P A * (Nplus P A * Nminus P C - Nminus P C * Nplus P A)
          = 2 * (Nplus P A * Nplus P A) * Nminus P C -
            Nplus P A * (Nplus P A * Nminus P C + Nminus P C * Nplus P A) := by noncomm_ring
        _ = -(Nplus P A * (Nplus P A * Nminus P C + Nminus P C * Nplus P A)) := by
            rw [Nplus_sq hP]; noncomm_ring
    dsimp [kleinReynolds4]
    rw [hmid, mul_zero, add_zero]
    calc casimirV P A C ^ 2 * Nplus P A + (sigmaOp P A C * Nplus P A) * sigmaOp P A C
        = casimirV P A C ^ 2 * Nplus P A + casimirV P A C * (Nplus P A * sigmaOp P A C) := by
          rw [hSigL]; noncomm_ring
      _ = 0 := by rw [hNpSig]; noncomm_ring
  have hNm : kleinReynolds4 P A C (Nminus P C) = 0 := by
    have hmid : phiOp P A C * Nminus P C * phiOp P A C - jOp P A C * Nminus P C * jOp P A C = 0 := by
      dsimp [phiOp, jOp]
      calc (Nplus P A + Nminus P C) * Nminus P C * (Nplus P A + Nminus P C) -
             (Nplus P A - Nminus P C) * Nminus P C * (Nplus P A - Nminus P C)
          = 2 * (Nplus P A * (Nminus P C * Nminus P C) + (Nminus P C * Nminus P C) * Nplus P A) := by
            noncomm_ring
        _ = 0 := by rw [Nminus_sq hP]; noncomm_ring
    have hSigL : sigmaOp P A C * Nminus P C = -(casimirV P A C * Nminus P C) := by
      dsimp [sigmaOp, casimirV, Qplus, Qminus]
      calc (Nplus P A * Nminus P C - Nminus P C * Nplus P A) * Nminus P C
          = 2 * Nplus P A * (Nminus P C * Nminus P C) -
            (Nplus P A * Nminus P C + Nminus P C * Nplus P A) * Nminus P C := by noncomm_ring
        _ = -((Nplus P A * Nminus P C + Nminus P C * Nplus P A) * Nminus P C) := by
            rw [Nminus_sq hP]; noncomm_ring
    have hNmSig : Nminus P C * sigmaOp P A C = casimirV P A C * Nminus P C := by
      rw [V_comm_Nminus hP]
      dsimp [sigmaOp, casimirV, Qplus, Qminus]
      calc Nminus P C * (Nplus P A * Nminus P C - Nminus P C * Nplus P A)
          = Nminus P C * (Nplus P A * Nminus P C + Nminus P C * Nplus P A) -
            2 * (Nminus P C * Nminus P C) * Nplus P A := by noncomm_ring
        _ = Nminus P C * (Nplus P A * Nminus P C + Nminus P C * Nplus P A) := by
            rw [Nminus_sq hP]; noncomm_ring
    dsimp [kleinReynolds4]
    rw [hmid, mul_zero, add_zero]
    calc casimirV P A C ^ 2 * Nminus P C + (sigmaOp P A C * Nminus P C) * sigmaOp P A C
        = casimirV P A C ^ 2 * Nminus P C - casimirV P A C * (Nminus P C * sigmaOp P A C) := by
          rw [hSigL]; noncomm_ring
      _ = 0 := by rw [hNmSig]; noncomm_ring
  have hPhi : kleinReynolds4 P A C (phiOp P A C) = 0 := by
    have hlin : kleinReynolds4 P A C (phiOp P A C) =
        kleinReynolds4 P A C (Nplus P A) + kleinReynolds4 P A C (Nminus P C) := by
      dsimp [kleinReynolds4, phiOp]; noncomm_ring
    rw [hlin, hNp, hNm, add_zero]
  have hV_klein : kleinReynolds4 P A C (casimirV P A C) = 4 * casimirV P A C ^ 3 := by
    have hcommPhi : phiOp P A C * casimirV P A C = casimirV P A C * phiOp P A C := by
      dsimp [phiOp]; rw [add_mul, mul_add, V_comm_Nplus hP, V_comm_Nminus hP]
    have hcommJ : jOp P A C * casimirV P A C = casimirV P A C * jOp P A C := by
      dsimp [jOp]; rw [sub_mul, mul_sub, V_comm_Nplus hP, V_comm_Nminus hP]
    have hcommSig : sigmaOp P A C * casimirV P A C = casimirV P A C * sigmaOp P A C := by
      dsimp [sigmaOp, casimirV]
      calc (Qplus P A C - Qminus P A C) * (Qplus P A C + Qminus P A C)
          = (Qplus P A C + Qminus P A C) * (Qplus P A C - Qminus P A C) +
            2 * (Qplus P A C * Qminus P A C - Qminus P A C * Qplus P A C) := by noncomm_ring
        _ = (Qplus P A C + Qminus P A C) * (Qplus P A C - Qminus P A C) := by
            rw [Qplus_mul_Qminus hP, Qminus_mul_Qplus hP]; noncomm_ring
    dsimp [kleinReynolds4]
    calc casimirV P A C ^ 2 * casimirV P A C +
           casimirV P A C * ((phiOp P A C * casimirV P A C) * phiOp P A C -
             (jOp P A C * casimirV P A C) * jOp P A C) +
           (sigmaOp P A C * casimirV P A C) * sigmaOp P A C
        = casimirV P A C * kleinReynolds4 P A C 1 := by
          dsimp [kleinReynolds4]; rw [hcommPhi, hcommJ, hcommSig]; noncomm_ring
      _ = 4 * casimirV P A C ^ 3 := by rw [h1]; noncomm_ring
  refine ⟨h1, hP_eval, hNp, hNm, hPhi, hV_klein, ?_, ?_⟩
  · dsimp [bogusReynolds]; rw [hV_klein]; noncomm_ring
  · dsimp [bogusReynolds]; rw [hPhi, zero_add]

/-- Scale-8 factored Klein Reynolds projector `Π⁽⁸⁾ = Π_Klein⁽⁴⁾ ∘ Π_diag⁽²⁾`:
    gives `8V²` on `1` while annihilating both off-diagonal corners `N₊` and `N₋`. -/
theorem factoredReynolds8_scale {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    factoredReynolds8 P A C 1 = 8 * casimirV P A C ^ 2 ∧
    factoredReynolds8 P A C (Nplus P A) = 0 ∧
    factoredReynolds8 P A C (Nminus P C) = 0 := by
  have hPP := P_mul_P hP
  have h1 := (kleinReynolds4_on_generators hP A C).1
  refine ⟨?_, ?_, ?_⟩
  · have hd1 : diagPinch2 P 1 = 2 := by
      dsimp [diagPinch2]
      calc 1 + (2 * P - 1) * 1 * (2 * P - 1)
          = (1 + 1) + 4 * (P * P - P) := by noncomm_ring
        _ = 2 := by rw [hPP, sub_self, mul_zero, add_zero, one_add_one_eq_two]
    have hk2 : kleinReynolds4 P A C 2 = 2 * kleinReynolds4 P A C 1 := by
      dsimp [kleinReynolds4]; noncomm_ring
    dsimp [factoredReynolds8]
    rw [hd1, hk2, h1]; noncomm_ring
  · have hdNp : diagPinch2 P (Nplus P A) = 0 := by
      dsimp [diagPinch2]
      calc Nplus P A + (2 * P - 1) * Nplus P A * (2 * P - 1)
          = 4 * (P * (Nplus P A * P)) - 2 * (P * Nplus P A) - 2 * (Nplus P A * P) +
            2 * Nplus P A := by noncomm_ring
        _ = 0 := by rw [Nplus_mul_P hP, P_mul_Nplus hP]; noncomm_ring
    dsimp [factoredReynolds8, kleinReynolds4]
    rw [hdNp]; noncomm_ring
  · have hdNm : diagPinch2 P (Nminus P C) = 0 := by
      dsimp [diagPinch2]
      calc Nminus P C + (2 * P - 1) * Nminus P C * (2 * P - 1)
          = 4 * ((P * Nminus P C) * P) - 2 * (P * Nminus P C) - 2 * (Nminus P C * P) +
            2 * Nminus P C := by noncomm_ring
        _ = 0 := by rw [P_mul_Nminus hP, Nminus_mul_P hP]; noncomm_ring
    dsimp [factoredReynolds8, kleinReynolds4]
    rw [hdNm]; noncomm_ring

/-- Abstract Klein Reynolds averaging `R_{S,T}(X)` over commuting involutions `S, T`
    is invariant under conjugation by `S`, `T`, and `ST`, scales by `4` on its own image,
    and annihilates every non-trivial character block `(εS, εT) ≠ (1, 1)`. -/
theorem involutionReynolds4_invariance_and_eigenblocks {B : Type*} [Ring B] {S T : B}
    (hS : S * S = 1) (hT : T * T = 1) (hST : S * T = T * S) :
    (∀ X : B, S * involutionReynolds4 S T X * S = involutionReynolds4 S T X) ∧
    (∀ X : B, T * involutionReynolds4 S T X * T = involutionReynolds4 S T X) ∧
    (∀ X : B, involutionReynolds4 S T (involutionReynolds4 S T X) =
      (4 : ℤ) • involutionReynolds4 S T X) ∧
    (∀ E : B, ∀ εS εT : ℤ,
      S * E * S = εS • E → T * E * T = εT • E →
      involutionReynolds4 S T E = ((1 + εS) * (1 + εT)) • E) := by
  have hSS : ∀ Z : B, S * (S * Z * S) * S = Z := fun Z => by
    calc S * (S * Z * S) * S = (S * S) * Z * (S * S) := by noncomm_ring
      _ = Z := by rw [hS]; noncomm_ring
  have hTT : ∀ Z : B, T * (T * Z * T) * T = Z := fun Z => by
    calc T * (T * Z * T) * T = (T * T) * Z * (T * T) := by noncomm_ring
      _ = Z := by rw [hT]; noncomm_ring
  have hConjS : ∀ X : B, S * involutionReynolds4 S T X * S = involutionReynolds4 S T X := by
    intro X
    dsimp [involutionReynolds4]
    have h1 : S * (T * X * T) * S = (S * T) * X * (T * S) := by noncomm_ring
    have h2 : S * ((S * T) * X * (T * S)) * S = T * X * T := by
      calc S * ((S * T) * X * (T * S)) * S
          = (S * S) * (T * X * T) * (S * S) := by noncomm_ring
        _ = T * X * T := by rw [hS]; noncomm_ring
    calc S * (X + S * X * S + T * X * T + (S * T) * X * (T * S)) * S
        = S * X * S + S * (S * X * S) * S + S * (T * X * T) * S +
            S * ((S * T) * X * (T * S)) * S := by noncomm_ring
      _ = S * X * S + X + (S * T) * X * (T * S) + T * X * T := by
          rw [hSS X, h1, h2]
      _ = X + S * X * S + T * X * T + (S * T) * X * (T * S) := by abel
  have hConjT : ∀ X : B, T * involutionReynolds4 S T X * T = involutionReynolds4 S T X := by
    intro X
    dsimp [involutionReynolds4]
    have hTS : T * S = S * T := hST.symm
    have h1 : T * (S * X * S) * T = (S * T) * X * (T * S) := by
      calc T * (S * X * S) * T = (T * S) * X * (S * T) := by noncomm_ring
        _ = (S * T) * X * (T * S) := by rw [hTS, hST]
    have h2 : T * ((S * T) * X * (T * S)) * T = S * X * S := by
      have hTST : T * (S * T) = (T * T) * S := by rw [hST]; noncomm_ring
      calc T * ((S * T) * X * (T * S)) * T
          = ((T * S) * T) * X * (T * (S * T)) := by noncomm_ring
        _ = ((S * T) * T) * X * ((T * T) * S) := by rw [hTS, hTST]
        _ = (S * (T * T)) * X * ((T * T) * S) := by noncomm_ring
        _ = S * X * S := by rw [hT]; noncomm_ring
    calc T * (X + S * X * S + T * X * T + (S * T) * X * (T * S)) * T
        = T * X * T + T * (S * X * S) * T + T * (T * X * T) * T +
            T * ((S * T) * X * (T * S)) * T := by noncomm_ring
      _ = T * X * T + (S * T) * X * (T * S) + X + S * X * S := by
          rw [hTT X, h1, h2]
      _ = X + S * X * S + T * X * T + (S * T) * X * (T * S) := by abel
  refine ⟨hConjS, hConjT, ?_, ?_⟩
  · intro X
    let Y := involutionReynolds4 S T X
    have hYS : S * Y * S = Y := hConjS X
    have hYT : T * Y * T = Y := hConjT X
    have hYST : (S * T) * Y * (T * S) = Y := by
      calc (S * T) * Y * (T * S) = S * (T * Y * T) * S := by noncomm_ring
        _ = Y := by rw [hYT, hYS]
    change Y + S * Y * S + T * Y * T + (S * T) * Y * (T * S) = (4 : ℤ) • Y
    rw [hYS, hYT, hYST]
    have h4 : (4 : ℤ) = 1 + 1 + 1 + 1 := rfl
    rw [h4, add_zsmul, add_zsmul, add_zsmul, one_zsmul]
  · intro E εS εT hES hET
    dsimp [involutionReynolds4]
    have hST_E : (S * T) * E * (T * S) = (εS * εT) • E := by
      calc (S * T) * E * (T * S) = S * (T * E * T) * S := by noncomm_ring
        _ = S * (εT • E) * S := by rw [hET]
        _ = εT • (S * E * S) := by simp only [smul_mul_assoc, mul_smul_comm]
        _ = εT • (εS • E) := by rw [hES]
        _ = (εS * εT) • E := by rw [smul_smul, mul_comm]
    rw [hES, hET, hST_E]
    have h4 : (1 + εS) * (1 + εT) = 1 + εS + εT + εS * εT := by ring
    rw [h4, add_zsmul, add_zsmul, add_zsmul, one_zsmul]

/-! ### 2. Hermitian Corner Equivalence vs. Asymmetric Corner Blindness (`F₄`) -/

lemma comm_P_decomp {B : Type*} [Ring B] (P A : B) :
    comm P A = Nplus P A - (1 - P) * A * P := by
  dsimp [comm, Nplus]; noncomm_ring

/-- Corner Faithfulness: Under `P* = P`, `A* = ±A`, and `X X* = 0 → X = 0`,
    `[P, A] ≠ 0 ↔ N₊ ≠ 0 ↔ V ≠ 0`. -/
theorem hermitian_corner_equivalence {B : Type*} [Ring B] [StarRing B]
    {P A : B} (hP : delta P = 0) (hP_star : star P = P)
    (hA_sym : star A = A ∨ star A = -A)
    (hfaith : ∀ X : B, X * star X = 0 → X = 0) :
    (comm P A ≠ 0 ↔ Nplus P A ≠ 0) ∧
    (Nplus P A ≠ 0 ↔ casimirV P A (star A) ≠ 0) := by
  have hNp_star : star (Nplus P A) = (1 - P) * star A * P := by
    dsimp [Nplus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  refine ⟨not_iff_not.mpr ?_, not_iff_not.mpr ?_⟩
  · constructor
    · intro hcomm
      have hPP := P_mul_P hP
      have hP1P : P * (1 - P) = 0 := by
        calc P * (1 - P) = P - P * P := by noncomm_ring
          _ = 0 := by rw [hPP, sub_self]
      calc Nplus P A
          = (P * P) * A * (1 - P) - (P * P) * A * (P * (1 - P)) -
              (P * (1 - P)) * A * P * (1 - P) := by
            rw [hPP, hP1P]; dsimp [Nplus]; noncomm_ring
        _ = P * comm P A * (1 - P) := by dsimp [comm]; noncomm_ring
        _ = 0 := by rw [hcomm]; noncomm_ring
    · intro hNp
      rw [comm_P_decomp P A, hNp, zero_sub, neg_eq_zero]
      have h0 : (1 - P) * star A * P = 0 := by
        rw [← hNp_star, hNp, star_zero]
      rcases hA_sym with hA | hA
      · rwa [hA] at h0
      · rw [hA] at h0
        calc (1 - P) * A * P = -((1 - P) * (-A) * P) := by noncomm_ring
          _ = 0 := by rw [h0, neg_zero]
  · constructor
    · intro hNp
      dsimp [casimirV, Qplus, Qminus]
      have hNm : Nminus P (star A) = 0 := by
        change (1 - P) * star A * P = 0
        rw [← hNp_star, hNp, star_zero]
      rw [hNp, hNm]; noncomm_ring
    · intro hV
      have hXX : Nplus P A * star (Nplus P A) = 0 := by
        rw [hNp_star]
        change Qplus P A (star A) = 0
        rw [← V_mul_P hP, hV, zero_mul]
      exact hfaith (Nplus P A) hXX

/-- Asymmetric Nilpotent Corner Blindness: in `Mat₂(ℤ)`, `P = E₁₁` and `X = E₁₂`
    satisfy `N₊ ≠ 0` (`[P, X] ≠ 0`) yet `N₋ = 0`, `Q₊ = Q₋ = V = Σ = 0`. -/
theorem asymmetric_corner_blindness :
    let P : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
    let X : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
    delta P = 0 ∧ comm P X ≠ 0 ∧ Nplus P X ≠ 0 ∧ Nminus P X = 0 ∧
    Qplus P X X = 0 ∧ Qminus P X X = 0 ∧ casimirV P X X = 0 ∧ sigmaOp P X X = 0 := by
  refine ⟨by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

/-! ### 3. Oblique Daughter Defect, Cayley Self-Adjoint Daughter & 4×4 Witness (`F₅..F₆`) -/

/-- Unipotent daughter conjugation defect audit and Gram defect law:
    `(1 - N₊)P(1 + N₊) = P + N₊` whereas `(1 + N₊)P(1 - N₊) = P - N₊`;
    for `P' = P - N₊`, `(P')* - P' = J` and `δ(P' (P')*) = Q₊² + Q₊`. -/
theorem oblique_daughter_defect_and_sign_audit {B : Type*} [Ring B] [StarRing B]
    {P : B} (hP : delta P = 0) (hP_star : star P = P) (A : B) :
    (1 - Nplus P A) * P * (1 + Nplus P A) = P + Nplus P A ∧
    (1 + Nplus P A) * P * (1 - Nplus P A) = P - Nplus P A ∧
    delta (P - Nplus P A) = 0 ∧
    star (P - Nplus P A) - (P - Nplus P A) = jOp P A (star A) ∧
    (P - Nplus P A) * star (P - Nplus P A) = P + Qplus P A (star A) ∧
    delta ((P - Nplus P A) * star (P - Nplus P A)) =
      Qplus P A (star A) ^ 2 + Qplus P A (star A) := by
  have hPP := P_mul_P hP
  have hNp_star : star (Nplus P A) = Nminus P (star A) := by
    dsimp [Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hGram : (P - Nplus P A) * star (P - Nplus P A) = P + Qplus P A (star A) := by
    rw [star_sub, hP_star, hNp_star]
    dsimp [Qplus]
    calc (P - Nplus P A) * (P - Nminus P (star A))
        = P * P - P * Nminus P (star A) - Nplus P A * P + Nplus P A * Nminus P (star A) := by
          noncomm_ring
      _ = P + Nplus P A * Nminus P (star A) := by
          rw [hPP, P_mul_Nminus hP, Nplus_mul_P hP]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, hGram, ?_⟩
  · calc (1 - Nplus P A) * P * (1 + Nplus P A)
        = (P - Nplus P A * P) * (1 + Nplus P A) := by noncomm_ring
      _ = P + P * Nplus P A := by rw [Nplus_mul_P hP]; noncomm_ring
      _ = P + Nplus P A := by rw [P_mul_Nplus hP]
  · calc (1 + Nplus P A) * P * (1 - Nplus P A)
        = (P + Nplus P A * P) * (1 - Nplus P A) := by noncomm_ring
      _ = P - P * Nplus P A := by rw [Nplus_mul_P hP]; noncomm_ring
      _ = P - Nplus P A := by rw [P_mul_Nplus hP]
  · dsimp [delta]
    calc (P - Nplus P A) ^ 2 - (P - Nplus P A)
        = (P * P - P) - (P * Nplus P A - Nplus P A) - Nplus P A * P +
          Nplus P A * Nplus P A := by noncomm_ring
      _ = 0 := by rw [hPP, P_mul_Nplus hP, Nplus_mul_P hP, Nplus_sq hP]; noncomm_ring
  · rw [star_sub, hP_star, hNp_star]; dsimp [jOp]; noncomm_ring
  · rw [hGram]
    have hPQ : P * Qplus P A (star A) = Qplus P A (star A) := by
      dsimp [Qplus]
      calc P * (Nplus P A * Nminus P (star A))
          = (P * Nplus P A) * Nminus P (star A) := by noncomm_ring
        _ = Nplus P A * Nminus P (star A) := by rw [P_mul_Nplus hP]
    have hQP : Qplus P A (star A) * P = Qplus P A (star A) := by
      dsimp [Qplus]
      calc (Nplus P A * Nminus P (star A)) * P
          = Nplus P A * (Nminus P (star A) * P) := by noncomm_ring
        _ = Nplus P A * Nminus P (star A) := by rw [Nminus_mul_P hP]
    dsimp [delta]
    calc (P + Qplus P A (star A)) ^ 2 - (P + Qplus P A (star A))
        = (P * P - P) + P * Qplus P A (star A) + Qplus P A (star A) * P -
          Qplus P A (star A) + Qplus P A (star A) ^ 2 := by noncomm_ring
      _ = Qplus P A (star A) ^ 2 + Qplus P A (star A) := by rw [hPP, hPQ, hQP]; noncomm_ring

theorem operator_pythagorean {B : Type*} [Ring B] {P : B} (hP : delta P = 0) (A C : B) :
    (1 - casimirV P A C) ^ 2 - 4 * jOp P A C ^ 2 = (1 + casimirV P A C) ^ 2 := by
  have hj2 : jOp P A C ^ 2 = -casimirV P A C := by rw [sq, jOp_sq hP]
  rw [hj2]
  noncomm_ring

/-- Square-root-free unitary Cayley cocycle `u_J = (1 - V + 2J)(1 + V)⁻¹` and exact
    self-adjoint daughter projector `P_sa = u_J P u_J*` in any `★`-ring where `1 + V` has inverse `W`. -/
theorem cayley_unitary_and_self_adjoint_daughter {B : Type*} [Ring B] [StarRing B]
    {P A W : B} (hP : delta P = 0) (hP_star : star P = P)
    (hVW : (1 + casimirV P A (star A)) * W = 1)
    (hWV : W * (1 + casimirV P A (star A)) = 1) :
    let V := casimirV P A (star A)
    let Φ := phiOp P A (star A)
    let J := jOp P A (star A)
    let u := (1 - V + 2 * J) * W
    let Psa := u * P * star u
    star u * u = 1 ∧ u * star u = 1 ∧
    star Psa = Psa ∧ delta Psa = 0 ∧
    Psa = ((1 - V) ^ 2 * P + 4 * V * (1 - P) - 2 * (1 - V) * Φ) * W ^ 2 := by
  intro V Φ J u Psa
  have hNp_star : star (Nplus P A) = Nminus P (star A) := by
    dsimp [Nplus, Nminus]; simp only [star_mul, star_sub, star_one, hP_star, mul_assoc]
  have hNm_star : star (Nminus P (star A)) = Nplus P A := by
    rw [← hNp_star, star_star]
  have hV_star : star V = V := by
    dsimp [V, casimirV, Qplus, Qminus]
    simp only [star_add, star_mul, hNp_star, hNm_star]
  have hJ_star : star J = -J := by
    dsimp [J, jOp]; simp only [star_sub, hNp_star, hNm_star]; noncomm_ring
  have hW_star : star W = W := by
    have h1V_star : star (1 + V) = 1 + V := by rw [star_add, star_one, hV_star]
    calc star W
        = star W * ((1 + V) * W) := by rw [hVW, mul_one]
      _ = (star W * star (1 + V)) * W := by rw [h1V_star, mul_assoc]
      _ = star ((1 + V) * W) * W := by rw [star_mul]
      _ = W := by rw [hVW, star_one, one_mul]
  have hW_comm_of_V : ∀ X : B, V * X = X * V → W * X = X * W := by
    intro X hVX
    have h1VX : (1 + V) * X = X * (1 + V) := by
      calc (1 + V) * X = X + V * X := by noncomm_ring
        _ = X + X * V := by rw [hVX]
        _ = X * (1 + V) := by noncomm_ring
    calc W * X
        = W * X * ((1 + V) * W) := by rw [hVW, mul_one]
      _ = W * (X * (1 + V)) * W := by noncomm_ring
      _ = (W * (1 + V)) * X * W := by rw [← h1VX]; noncomm_ring
      _ = X * W := by rw [hWV, one_mul]
  have hVP_comm : V * P = P * V := comm_V_P hP A (star A)
  have hVNp_comm : V * Nplus P A = Nplus P A * V := V_comm_Nplus hP A (star A)
  have hVNm_comm : V * Nminus P (star A) = Nminus P (star A) * V := V_comm_Nminus hP A (star A)
  have hVJ_comm : V * J = J * V := by
    dsimp [J, jOp]; rw [mul_sub, sub_mul, hVNp_comm, hVNm_comm]
  have hWP_comm : W * P = P * W := hW_comm_of_V P hVP_comm
  have hWJ_comm : W * J = J * W := hW_comm_of_V J hVJ_comm
  have hWV_comm : W * V = V * W := hW_comm_of_V V rfl
  have hu_star : star u = W * (1 - V - 2 * J) := by
    dsimp [u]
    simp only [star_mul, star_add, star_sub, star_one, star_ofNat, hW_star, hV_star, hJ_star]
    noncomm_ring
  have hprod1 : (1 - V - 2 * J) * (1 - V + 2 * J) = (1 + V) ^ 2 := by
    calc (1 - V - 2 * J) * (1 - V + 2 * J)
        = (1 - V) ^ 2 + 2 * (J * V - V * J) - 4 * J ^ 2 := by noncomm_ring
      _ = (1 - V) ^ 2 - 4 * J ^ 2 := by rw [hVJ_comm]; noncomm_ring
      _ = (1 + V) ^ 2 := operator_pythagorean hP A (star A)
  have hprod2 : (1 - V + 2 * J) * (1 - V - 2 * J) = (1 + V) ^ 2 := by
    calc (1 - V + 2 * J) * (1 - V - 2 * J)
        = (1 - V) ^ 2 - 2 * (J * V - V * J) - 4 * J ^ 2 := by noncomm_ring
      _ = (1 - V) ^ 2 - 4 * J ^ 2 := by rw [hVJ_comm]; noncomm_ring
      _ = (1 + V) ^ 2 := operator_pythagorean hP A (star A)
  have huu1 : star u * u = 1 := by
    dsimp [u]; rw [hu_star]
    calc W * (1 - V - 2 * J) * ((1 - V + 2 * J) * W)
        = W * ((1 - V - 2 * J) * (1 - V + 2 * J)) * W := by noncomm_ring
      _ = W * (1 + V) ^ 2 * W := by rw [hprod1]
      _ = (W * (1 + V)) * ((1 + V) * W) := by noncomm_ring
      _ = 1 := by rw [hWV, hVW, one_mul]
  have huu2 : u * star u = 1 := by
    have hu_alt : u = W * (1 - V + 2 * J) := by
      dsimp [u]
      calc (1 - V + 2 * J) * W = W - V * W + 2 * (J * W) := by noncomm_ring
        _ = W - W * V + 2 * (W * J) := by rw [← hWV_comm, ← hWJ_comm]
        _ = W * (1 - V + 2 * J) := by noncomm_ring
    have hustar_alt : star u = (1 - V - 2 * J) * W := by
      rw [hu_star]
      calc W * (1 - V - 2 * J) = W - W * V - 2 * (W * J) := by noncomm_ring
        _ = W - V * W - 2 * (J * W) := by rw [hWV_comm, hWJ_comm]
        _ = (1 - V - 2 * J) * W := by noncomm_ring
    rw [hustar_alt, hu_alt]
    calc W * (1 - V + 2 * J) * ((1 - V - 2 * J) * W)
        = W * ((1 - V + 2 * J) * (1 - V - 2 * J)) * W := by noncomm_ring
      _ = W * (1 + V) ^ 2 * W := by rw [hprod2]
      _ = (W * (1 + V)) * ((1 + V) * W) := by noncomm_ring
      _ = 1 := by rw [hWV, hVW, one_mul]
  refine ⟨huu1, huu2, ?_, ?_, ?_⟩
  · dsimp [Psa]; simp only [star_mul, star_star, hP_star, mul_assoc]
  · dsimp [Psa, delta]
    calc (u * P * star u) ^ 2 - u * P * star u
        = u * P * (star u * u) * P * star u - u * P * star u := by noncomm_ring
      _ = u * (P * P) * star u - u * P * star u := by rw [huu1]; noncomm_ring
      _ = 0 := by rw [P_mul_P hP]; noncomm_ring
  · have hustar_alt : star u = (1 - V - 2 * J) * W := by
      rw [hu_star]
      calc W * (1 - V - 2 * J) = W - W * V - 2 * (W * J) := by noncomm_ring
        _ = W - V * W - 2 * (J * W) := by rw [hWV_comm, hWJ_comm]
        _ = (1 - V - 2 * J) * W := by noncomm_ring
    have hW_mid : W * P * (1 - V - 2 * J) = P * (1 - V - 2 * J) * W := by
      calc W * P * (1 - V - 2 * J)
          = P * (W - W * V - 2 * (W * J)) := by rw [hWP_comm]; noncomm_ring
        _ = P * (1 - V - 2 * J) * W := by rw [hWV_comm, hWJ_comm]; noncomm_ring
    have hJP : J * P = -Nminus P (star A) := by
      dsimp [J, jOp]
      calc (Nplus P A - Nminus P (star A)) * P
          = Nplus P A * P - Nminus P (star A) * P := by noncomm_ring
        _ = -Nminus P (star A) := by rw [Nplus_mul_P hP, Nminus_mul_P hP]; noncomm_ring
    have hPJ : P * J = Nplus P A := by
      dsimp [J, jOp]
      calc P * (Nplus P A - Nminus P (star A))
          = P * Nplus P A - P * Nminus P (star A) := by noncomm_ring
        _ = Nplus P A := by rw [P_mul_Nplus hP, P_mul_Nminus hP]; noncomm_ring
    have hNmJ : Nminus P (star A) * J = V * (1 - P) := by
      have hNmNp : Nminus P (star A) * Nplus P A = V * (1 - P) := by
        calc Nminus P (star A) * Nplus P A
            = V - V * P := by rw [V_mul_P hP]; dsimp [V, casimirV, Qplus, Qminus]; noncomm_ring
          _ = V * (1 - P) := by noncomm_ring
      dsimp [J, jOp]
      calc Nminus P (star A) * (Nplus P A - Nminus P (star A))
          = Nminus P (star A) * Nplus P A - Nminus P (star A) * Nminus P (star A) := by
            noncomm_ring
        _ = V * (1 - P) := by rw [Nminus_sq hP, hNmNp]; noncomm_ring
    have hPV_sub : P * (1 - V) = (1 - V) * P := by
      calc P * (1 - V) = P - P * V := by noncomm_ring
        _ = P - V * P := by rw [← hVP_comm]
        _ = (1 - V) * P := by noncomm_ring
    have hNmV_sub : Nminus P (star A) * (1 - V) = (1 - V) * Nminus P (star A) := by
      calc Nminus P (star A) * (1 - V)
          = Nminus P (star A) - Nminus P (star A) * V := by noncomm_ring
        _ = Nminus P (star A) - V * Nminus P (star A) := by rw [← hVNm_comm]
        _ = (1 - V) * Nminus P (star A) := by noncomm_ring
    have hcore : (1 - V + 2 * J) * P * (1 - V - 2 * J) =
        (1 - V) ^ 2 * P + 4 * V * (1 - P) - 2 * (1 - V) * Φ := by
      dsimp [Φ, phiOp]
      calc (1 - V + 2 * J) * P * (1 - V - 2 * J)
          = ((1 - V) * P + 2 * (J * P)) * (1 - V - 2 * J) := by noncomm_ring
        _ = ((1 - V) * P - 2 * Nminus P (star A)) * (1 - V - 2 * J) := by
            rw [hJP]; noncomm_ring
        _ = (1 - V) * (P * (1 - V)) - 2 * (1 - V) * (P * J) -
            2 * (Nminus P (star A) * (1 - V)) + 4 * (Nminus P (star A) * J) := by noncomm_ring
        _ = (1 - V) ^ 2 * P + 4 * V * (1 - P) -
            2 * (1 - V) * (Nplus P A + Nminus P (star A)) := by
            rw [hPV_sub, hPJ, hNmV_sub, hNmJ]; noncomm_ring
    dsimp [Psa, u]
    rw [hustar_alt]
    calc (1 - V + 2 * J) * W * P * ((1 - V - 2 * J) * W)
        = (1 - V + 2 * J) * (W * P * (1 - V - 2 * J)) * W := by noncomm_ring
      _ = ((1 - V + 2 * J) * P * (1 - V - 2 * J)) * W ^ 2 := by rw [hW_mid]; noncomm_ring
      _ = ((1 - V) ^ 2 * P + 4 * V * (1 - P) - 2 * (1 - V) * Φ) * W ^ 2 := by rw [hcore]

/-- Non-scalar `Mat₄(ℝ)` witness (`V = diag(1, 4, 1, 4)` non-central in `Mat₄(ℝ)`). -/
def P4_Z : Matrix (Fin 4) (Fin 4) ℤ := Matrix.diagonal ![1, 1, 0, 0]
def A4_Z : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
     0, 0, 0, 2;
     1, 0, 0, 0;
     0, 2, 0, 0]
def tenW4_Z : Matrix (Fin 4) (Fin 4) ℤ := Matrix.diagonal ![5, 2, 5, 2]
def probe4_Z : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

def toMat4R : Matrix (Fin 4) (Fin 4) ℤ →+* Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix

def P4 : Matrix (Fin 4) (Fin 4) ℝ := toMat4R P4_Z
def A4 : Matrix (Fin 4) (Fin 4) ℝ := toMat4R A4_Z
def W4 : Matrix (Fin 4) (Fin 4) ℝ := (1 / 10 : ℝ) • toMat4R tenW4_Z
def probe4 : Matrix (Fin 4) (Fin 4) ℝ := toMat4R probe4_Z

lemma star_toMat4R (M : Matrix (Fin 4) (Fin 4) ℤ) :
    star (toMat4R M) = toMat4R M.transpose := by
  ext i j
  simp [toMat4R]

/-- Master Non-Vacuity Theorem in `Mat₄(ℝ)`: `(P₄, A₄, W₄)` realizes a strictly non-scalar
    Casimir `V = diag(1, 4, 1, 4)` (`δ(V) ≠ 0`, `comm V probe₄ ≠ 0`), oblique unipotent
    breakdown, and exact unitary Cayley patching `P_sa* = P_sa = P_sa²`. -/
theorem peirce_defect_nonscalar_witness :
    delta P4 = 0 ∧ star P4 = P4 ∧ star A4 = A4 ∧
    delta (casimirV P4 A4 (star A4)) ≠ 0 ∧
    (∀ c : ℝ, casimirV P4 A4 (star A4) ≠ c • (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    comm (casimirV P4 A4 (star A4)) probe4 ≠ 0 ∧
    star (P4 - Nplus P4 A4) ≠ P4 - Nplus P4 A4 ∧
    let V := casimirV P4 A4 (star A4)
    let u := (1 - V + 2 * jOp P4 A4 (star A4)) * W4
    let Psa := u * P4 * star u
    star u * u = 1 ∧ u * star u = 1 ∧ star Psa = Psa ∧ delta Psa = 0 := by
  have hP : delta P4 = 0 := by
    change P4 ^ 2 - P4 = 0
    rw [P4, ← map_pow, ← map_sub, show P4_Z ^ 2 - P4_Z = 0 by decide, map_zero]
  have hPs : star P4 = P4 := by
    rw [P4, star_toMat4R, show P4_Z.transpose = P4_Z by decide]
  have hAs : star A4 = A4 := by
    rw [A4, star_toMat4R, show A4_Z.transpose = A4_Z by decide]
  have hV_eq : casimirV P4 A4 (star A4) = toMat4R (casimirV P4_Z A4_Z A4_Z) := by
    rw [hAs]
    simp [casimirV, Qplus, Qminus, Nplus, Nminus, P4, A4, map_add, map_sub, map_mul, map_one]
  have hVW_Z : (1 + casimirV P4_Z A4_Z A4_Z) * tenW4_Z = (10 : ℤ) • 1 := by decide
  have hWV_Z : tenW4_Z * (1 + casimirV P4_Z A4_Z A4_Z) = (10 : ℤ) • 1 := by decide
  have hVW : (1 + casimirV P4 A4 (star A4)) * W4 = 1 := by
    rw [hV_eq, W4, mul_smul_comm, ← map_one toMat4R, ← map_add, ← map_mul, hVW_Z,
        map_zsmul, map_one, ← Int.cast_smul_eq_zsmul ℝ (10 : ℤ), smul_smul]
    norm_num
  have hWV : W4 * (1 + casimirV P4 A4 (star A4)) = 1 := by
    rw [hV_eq, W4, smul_mul_assoc, ← map_one toMat4R, ← map_add, ← map_mul, hWV_Z,
        map_zsmul, map_one, ← Int.cast_smul_eq_zsmul ℝ (10 : ℤ), smul_smul]
    norm_num
  obtain ⟨hu1, hu2, hPsa_s, hPsa_d, _⟩ :=
    cayley_unitary_and_self_adjoint_daughter hP hPs hVW hWV
  refine ⟨hP, hPs, hAs, ?_, ?_, ?_, ?_, hu1, hu2, hPsa_s, hPsa_d⟩
  · intro hdel
    rw [delta, hV_eq, ← map_pow, ← map_sub] at hdel
    have h11 := congr_fun (congr_fun hdel 1) 1
    simp only [toMat4R, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
               Matrix.zero_apply, Int.cast_eq_zero] at h11
    revert h11; decide
  · intro c hc
    rw [hV_eq] at hc
    have h00 := congr_fun (congr_fun hc 0) 0
    have h11 := congr_fun (congr_fun hc 1) 1
    have h00_val : casimirV P4_Z A4_Z A4_Z 0 0 = 1 := by decide
    have h11_val : casimirV P4_Z A4_Z A4_Z 1 1 = 4 := by decide
    simp only [toMat4R, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
               Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one, ↓reduceIte,
               h00_val, h11_val] at h00 h11
    norm_num at h00 h11
    rw [← h00] at h11
    revert h11
    norm_num
  · intro hcomm
    rw [comm, hV_eq, probe4, ← map_mul, ← map_mul, ← map_sub] at hcomm
    have h01 := congr_fun (congr_fun hcomm 0) 1
    simp only [toMat4R, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
               Matrix.zero_apply, Int.cast_eq_zero] at h01
    revert h01; decide
  · intro h_ob
    have hj := (oblique_daughter_defect_and_sign_audit hP hPs A4).2.2.2.1
    rw [h_ob, sub_self, hAs] at hj
    have hj_map : toMat4R (jOp P4_Z A4_Z A4_Z) = 0 := by
      simpa [jOp, Nplus, Nminus, P4, A4, map_sub, map_mul, map_one] using hj.symm
    have h02 := congr_fun (congr_fun hj_map 0) 2
    simp only [toMat4R, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
               Matrix.zero_apply, Int.cast_eq_zero] at h02
    revert h02; decide

/-! ### 4. Support-Projected Operator Coercivity (`F₇`) -/

/-- Support-Projected Operator Coercivity Factorization: whenever `Π_V` supports `V`
    (`Π_V * V = V` and `V * Π_V = V`), `V^2 - m^2 • V = V * (V - m^2 • Π_V)` while `V`
    annihilates `1 - Π_V` on both sides. -/
theorem support_projected_coercivity_factorization {B : Type*} [Ring B] [Algebra ℝ B]
    {V supportProj : B} (hSupportLeft : supportProj * V = V)
    (hSupportRight : V * supportProj = V) (m : ℝ) :
    V * V - (m ^ 2) • V = V * (V - (m ^ 2) • supportProj) ∧
    (1 - supportProj) * V = 0 ∧
    V * (1 - supportProj) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_sub, mul_smul_comm, hSupportRight]
  · calc (1 - supportProj) * V = V - supportProj * V := by noncomm_ring
      _ = 0 := by rw [hSupportLeft, sub_self]
  · calc V * (1 - supportProj) = V - V * supportProj := by noncomm_ring
      _ = 0 := by rw [hSupportRight, sub_self]

/-- Non-scalar `Mat₃(ℝ)` refutation of the scalar gap dichotomy: `V = diag(2, 3, 0)` and
    `Π_V = diag(1, 1, 0)` have nontrivial kernel `1 - Π_V ≠ 0`, `V` is NOT a scalar multiple
    of `Π_V`, yet `V - 1² • Π_V` and `V² - 1² • V` are both positive semidefinite. -/
theorem support_coercivity_refutes_scalar_dichotomy :
    let V : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![2, 3, 0]
    let supportProj : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, 0]
    supportProj * supportProj = supportProj ∧ supportProj * V = V ∧ V * supportProj = V ∧
    (1 - supportProj) ≠ 0 ∧
    (∀ c : ℝ, V ≠ c • supportProj) ∧
    Matrix.PosSemidef (V - (1 ^ 2 : ℝ) • supportProj) ∧
    Matrix.PosSemidef (V * V - (1 ^ 2 : ℝ) • V) := by
  intro V supportProj
  have hSupportSq : supportProj * supportProj = supportProj := by
    dsimp [supportProj]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hSupportV : supportProj * V = V := by
    dsimp [supportProj, V]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hVSupport : V * supportProj = V := by
    dsimp [supportProj, V]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨hSupportSq, hSupportV, hVSupport, ?_, ?_, ?_, ?_⟩
  · intro h
    have h22 := congr_fun (congr_fun h 2) 2
    simp [supportProj] at h22
  · intro c hc
    have h00 := congr_fun (congr_fun hc 0) 0
    have h11 := congr_fun (congr_fun hc 1) 1
    simp [V, supportProj] at h00 h11
    linarith
  · have hdiag : V - (1 ^ 2 : ℝ) • supportProj = Matrix.diagonal ![1, 2, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [V, supportProj] <;> norm_num
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · have hdiag : V * V - (1 ^ 2 : ℝ) • V = Matrix.diagonal ![2, 6, 0] := by
      dsimp [V]
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> norm_num
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num

/-! ### 5. Non-Commutation of Spectral Mass Gaps with Inductive Shell Colimits (`F₈..F₉`) -/

/-- Scalar shell colimit counterexample: `gap_n = 1 / (n + 1)` is strictly positive for
    every `n : ℕ` and converges to `0`, so no uniform mass gap `m > 0` holds across all shells. -/
theorem colimit_shell_positivity_without_gap :
    let gap : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    (∀ n : ℕ, 0 < gap n) ∧
    Filter.Tendsto gap Filter.atTop (nhds 0) ∧
    ¬ ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, m ≤ gap n := by
  intro gap
  refine ⟨fun n => by dsimp [gap]; positivity, ?_, ?_⟩
  · simpa [gap] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · rintro ⟨m, hm, hbound⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / m)
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmn : m ≤ 1 / ((n : ℝ) + 1) := hbound n
    have h1 : m * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ hn_pos).mp hmn
    have h2 : 1 < m * (n : ℝ) := (div_lt_iff₀' hm).mp hn
    nlinarith

/-- Finite-shell diagonal operator `V_shell n = diag(1, 1/2, ..., 1/(n+1))`. -/
def V_shell (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal fun k : Fin (n + 1) => 1 / ((k : ℝ) + 1)

/-- Isometric upper-left shell transition embedding `Mat_{n+1}(ℝ) →ₗ[ℝ] Mat_{n+2}(ℝ)`. -/
def embedShell (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →ₗ[ℝ] Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ where
  toFun M := Matrix.of fun i j =>
    Fin.lastCases 0 (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i
  map_add' M N := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp
  map_smul' r M := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp

/-- Operator-Level Colimit Non-Commutation Theorem: the tower `(V_shell n)` has compatible
    upper-left embeddings, is strictly positive definite (`Matrix.PosDef`) with explicit gap
    `1 / (n + 1)` at EVERY finite stage `n : ℕ`, yet admits NO uniform positive spectral mass gap
    `m > 0` satisfying `V_shell n ≥_psd m² • 1` across all stages. -/
theorem matrix_tower_positive_shells_without_uniform_gap :
    (∀ (n : ℕ) (i j : Fin (n + 1)),
      V_shell (n + 1) (Fin.castSucc i) (Fin.castSucc j) = V_shell n i j) ∧
    (∀ (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)),
      embedShell n M (Fin.castSucc i) (Fin.castSucc j) = M i j) ∧
    (∀ n : ℕ, Matrix.PosDef (V_shell n)) ∧
    (∀ n : ℕ, Matrix.PosSemidef (V_shell n - (1 / ((n : ℝ) + 1)) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))) ∧
    ¬ ∃ m : ℝ, 0 < m ∧
      ∀ n : ℕ, Matrix.PosSemidef (V_shell n - (m ^ 2) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) := by
  have hsmul1 : ∀ (n : ℕ) (c : ℝ),
      V_shell n - c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
        Matrix.diagonal fun k : Fin (n + 1) => 1 / ((k : ℝ) + 1) - c := by
    intro n c
    ext i j
    by_cases hij : i = j <;> simp [V_shell, hij]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n i j
    by_cases hij : i = j
    · subst hij
      simp [V_shell]
    · have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
      simp [V_shell, hij, hij']
  · intro n M i j
    simp [embedShell]
  · intro n
    dsimp [V_shell]
    exact Matrix.PosDef.diagonal fun k => by positivity
  · intro n
    rw [hsmul1, Matrix.posSemidef_diagonal_iff]
    intro k
    have hk : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hkn : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
      exact_mod_cast Nat.succ_le_succ hkn
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos hk
    linarith
  · rintro ⟨m, hm, hpsd⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / m ^ 2)
    have hdiag := hpsd n
    rw [hsmul1, Matrix.posSemidef_diagonal_iff] at hdiag
    have hlast := hdiag (Fin.last n)
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have h1 : m ^ 2 * ((n : ℝ) + 1) ≤ 1 := by
      have hle : m ^ 2 ≤ 1 / ((n : ℝ) + 1) := by simpa using hlast
      exact (le_div_iff₀ hn_pos).mp hle
    have h2 : 1 < m ^ 2 * (n : ℝ) := (div_lt_iff₀' hm2).mp hn
    nlinarith

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
