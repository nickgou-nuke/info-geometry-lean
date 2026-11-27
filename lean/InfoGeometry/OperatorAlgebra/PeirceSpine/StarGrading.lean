/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Star reversal and grading-twisted anti-involution

Algebraic content of transcript turns 222 and 227. The carrier is an arbitrary
star-ring, not a scalar model. A self-adjoint idempotent supplies the grading.
No positivity, norm, probability, or Hilbert-space assertion is made.
Dependency order: star reversal of corners → star table of generators;
self-adjoint grading → twisted anti-involution → principal-ideal/chart duality.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B] {P : B} (hPs : star P = P)
include hPs

theorem star_conePlus (A : B) : star (conePlus P A) = coneMinus P (star A) := by
  simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]

theorem star_coneMinus (A : B) : star (coneMinus P A) = conePlus P (star A) := by
  simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]

theorem star_invS : star (invS P) = invS P := by
  simp only [invS, star_sub, star_one, hPs]

theorem star_genPhi (A : B) : star (genPhi P A (star A)) = genPhi P A (star A) := by
  simp only [genPhi, star_add, star_conePlus hPs, star_coneMinus hPs, star_star]
  exact add_comm _ _

theorem star_genJ (A : B) : star (genJ P A (star A)) = -genJ P A (star A) := by
  simp only [genJ, star_sub, star_conePlus hPs, star_coneMinus hPs, star_star, neg_sub]

theorem star_genV (A : B) : star (genV P A (star A)) = genV P A (star A) := by
  simp only [genV, anticomm, star_add, star_mul, star_conePlus hPs,
    star_coneMinus hPs, star_star]

theorem star_genSig (A : B) : star (genSig P A (star A)) = genSig P A (star A) := by
  simp only [genSig, comm, star_sub, star_mul, star_conePlus hPs,
    star_coneMinus hPs, star_star]

variable (hP : P * P = P)
include hP

theorem grading_star_involutive (X : B) :
    invS P * star (invS P * star X * invS P) * invS P = X := by
  simp only [star_mul, star_invS hPs, star_star]
  peirce_nf hP

omit hPs in
/-- Product reversal requires the grading square, not self-adjointness. -/
theorem grading_star_mul (X Y : B) :
    invS P * star (X * Y) * invS P =
      (invS P * star Y * invS P) * (invS P * star X * invS P) := by
  rw [star_mul]
  peirce_nf hP

theorem grading_star_left_ideal (X : B) :
    invS P * star (X * P) * invS P = P * (invS P * star X * invS P) := by
  rw [star_mul, hPs]
  peirce_nf hP

theorem grading_star_right_ideal (X : B) :
    invS P * star (P * X) * invS P = (invS P * star X * invS P) * P := by
  rw [star_mul, hPs]
  peirce_nf hP

theorem grading_star_upper_chart (A : B) :
    invS P * star (P - conePlus P A) * invS P = P + coneMinus P (star A) := by
  rw [star_sub, hPs, star_conePlus hPs]
  peirce_nf hP

theorem grading_star_lower_chart (A : B) :
    invS P * star (P + coneMinus P A) * invS P = P - conePlus P (star A) := by
  rw [star_add, hPs, star_coneMinus hPs]
  peirce_nf hP

theorem grading_star_genPhi (A : B) :
    invS P * star (genPhi P A (star A)) * invS P = -genPhi P A (star A) := by
  rw [star_genPhi hPs]
  peirce_nf hP

theorem grading_star_genJ (A : B) :
    invS P * star (genJ P A (star A)) * invS P = genJ P A (star A) := by
  rw [star_genJ hPs]
  peirce_nf hP

theorem grading_star_genV (A : B) :
    invS P * star (genV P A (star A)) * invS P = genV P A (star A) := by
  rw [star_genV hPs]
  peirce_nf hP

theorem grading_star_genSig (A : B) :
    invS P * star (genSig P A (star A)) * invS P = genSig P A (star A) := by
  rw [star_genSig hPs]
  peirce_nf hP

omit hPs hP

/-- Symmetric part `W + W⋆` of an operator in a star-ring (DIGRAC symmetric component). -/
def digracSym (W : B) : B := W + star W

/-- Skew-adjoint part `W - W⋆` of an operator in a star-ring (DIGRAC flow-imbalance component). -/
def digracImb (W : B) : B := W - star W

/-- Parity-twisted self-adjoint sum `S N₊ + N₊⋆ S` (MagNet adjacency operator). -/
def magnetAdj (P A : B) : B :=
  invS P * conePlus P A + star (conePlus P A) * invS P

/-- Operator difference `D - (S N₊ + N₊⋆ S)` (MagNet Laplacian operator). -/
def magnetLaplacian (P D A : B) : B := D - magnetAdj P A

include hPs hP

/-- **DIGRAC Directed Adjacency Decomposition & MagNet Magnetic Laplacian**:
1. Any operator `W` splits into its symmetric part `digracSym W = W + W⋆` and
   skew-adjoint flow-imbalance part `digracImb W = W - W⋆`, with
   `digracSym W + digracImb W = 2 W`, `(digracSym W)⋆ = digracSym W`, and
   `(digracImb W)⋆ = -digracImb W`.
2. On the directed corner `W = N₊ = P A (1 - P)` with self-adjoint `P`, the
   symmetric and skew-adjoint components recover `Φ = N₊ + N₋` and `J = N₊ - N₋`
   with `C = A⋆`, and `(digracImb N₊)² = -V`.
3. Twisting `N₊` and its adjoint on opposite sides by the grading involution
   `S = 2P - 1` produces the self-adjoint operator
   `magnetAdj P A = S N₊ + N₊⋆ S = S J = -J S = Φ`, whose square is `+V`.
   (The order and sign matter: `J S` alone is `-Φ`.) For any self-adjoint
   degree operator `D⋆ = D`, `magnetLaplacian P D A` is self-adjoint. -/
theorem digrac_flow_imbalance_and_magnet_laplacian (W A D : B) :
    digracSym W + digracImb W = (2 : ℤ) • W ∧
    star (digracSym W) = digracSym W ∧
    star (digracImb W) = -digracImb W ∧
    digracSym (conePlus P A) = genPhi P A (star A) ∧
    digracImb (conePlus P A) = genJ P A (star A) ∧
    digracImb (conePlus P A) * digracImb (conePlus P A) = -genV P A (star A) ∧
    magnetAdj P A = invS P * genJ P A (star A) ∧
    star (magnetAdj P A) = magnetAdj P A ∧
    (star D = D → star (magnetLaplacian P D A) = magnetLaplacian P D A) ∧
    magnetAdj P A * magnetAdj P A = genV P A (star A) := by
  have hMagStar : star (magnetAdj P A) = magnetAdj P A := by
    simp only [magnetAdj, star_add, star_mul, star_invS hPs, star_star, add_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hMagStar, ?_, ?_⟩
  · unfold digracSym digracImb
    abel_nf
  · simp only [digracSym, star_add, star_star, add_comm]
  · simp only [digracImb, star_sub, star_star, neg_sub]
  · rw [digracSym, star_conePlus hPs, genPhi]
  · rw [digracImb, star_conePlus hPs, genJ]
  · rw [digracImb, star_conePlus hPs]
    peirce_nf hP
  · rw [magnetAdj, star_conePlus hPs]
    peirce_nf hP
  · intro hD
    simp only [magnetLaplacian, star_sub, hD, hMagStar]
  · rw [magnetAdj, star_conePlus hPs]
    peirce_nf hP

/-! ### Complete 2x2 Peirce-Corner Involution Classification

Every involution `φ` on an associative star-ring `B` split by an idempotent `P`
with `Q = 1 - P` falls into one of four quadrants determined by
(multiplicative vs. anti-multiplicative) × (fixes `P, Q` vs. swaps `P ↔ Q`):
1. Chiral grading (`Ad_{invS P}`): multiplicative, fixes `P, Q` (negates soul corners).
2. Sheet swap (`μ`): multiplicative, swaps `P ↔ Q` (swaps soul corners `N₊ ↔ N₋`).
3. Star involution (`*`): anti-multiplicative, fixes `P, Q` (swaps soul corners `N₊ ↔ N₋`).
4. Anti-multiplicative sheet swap (`τ`): anti-multiplicative, swaps `P ↔ Q`
   (double-reversal cancellation preserves each chiral corner `N₊` and `N₋`). -/

section PeirceCornerInvolutionTable

omit [StarRing B] hPs hP

private lemma invS_mul_P {P : B} (hP : P * P = P) : invS P * P = P := by
  dsimp [invS]
  rw [sub_mul, sub_mul, one_mul, hP, sub_self, sub_zero]

private lemma P_mul_invS {P : B} (hP : P * P = P) : P * invS P = P := by
  dsimp [invS]
  rw [mul_sub, mul_sub, mul_one, hP, sub_self, sub_zero]

private lemma invS_mul_oneSub {P : B} (hP : P * P = P) : invS P * (1 - P) = -(1 - P) := by
  dsimp [invS]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  abel

private lemma oneSub_mul_invS {P : B} (hP : P * P = P) : (1 - P) * invS P = -(1 - P) := by
  dsimp [invS]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  abel

/-- **Row 1 (Chiral Grading `Ad_{invS P}`)**: multiplicative conjugation fixing `P, 1 - P`
fixes the even body corners and negates each odd chiral soul corner. -/
theorem chiralGrading_ad_corners {P : B} (hP : P * P = P) (X : B) :
    invS P * peirce11 P X * invS P = peirce11 P X ∧
    invS P * peirce00 P X * invS P = peirce00 P X ∧
    invS P * conePlus P X * invS P = -conePlus P X ∧
    invS P * coneMinus P X * invS P = -coneMinus P X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [peirce11]
    calc invS P * (P * X * P) * invS P
        = (invS P * P) * X * (P * invS P) := by noncomm_ring
      _ = P * X * P := by rw [invS_mul_P hP, P_mul_invS hP]
  · dsimp [peirce00]
    calc invS P * ((1 - P) * X * (1 - P)) * invS P
        = (invS P * (1 - P)) * X * ((1 - P) * invS P) := by noncomm_ring
      _ = (-(1 - P)) * X * (-(1 - P)) := by rw [invS_mul_oneSub hP, oneSub_mul_invS hP]
      _ = (1 - P) * X * (1 - P) := by noncomm_ring
  · dsimp [conePlus]
    calc invS P * (P * X * (1 - P)) * invS P
        = (invS P * P) * X * ((1 - P) * invS P) := by noncomm_ring
      _ = P * X * (-(1 - P)) := by rw [invS_mul_P hP, oneSub_mul_invS hP]
      _ = -(P * X * (1 - P)) := by noncomm_ring
  · dsimp [coneMinus]
    calc invS P * ((1 - P) * X * P) * invS P
        = (invS P * (1 - P)) * X * (P * invS P) := by noncomm_ring
      _ = (-(1 - P)) * X * P := by rw [invS_mul_oneSub hP, P_mul_invS hP]
      _ = -((1 - P) * X * P) := by noncomm_ring

/-- In any ring without additive 2-torsion, a single-corner state fixed by Row 1
(`Ad_{invS P}`) vanishes. -/
theorem chiralGrading_ad_singleCorner_fixed_zero {P : B} (hP : P * P = P)
    (hNo2 : ∀ z : B, z + z = 0 → z = 0) (X : B) :
    (invS P * conePlus P X * invS P = conePlus P X → conePlus P X = 0) ∧
    (invS P * coneMinus P X * invS P = coneMinus P X → coneMinus P X = 0) := by
  have hc := chiralGrading_ad_corners hP X
  refine ⟨fun h => hNo2 _ ?_, fun h => hNo2 _ ?_⟩
  · have hneg : -conePlus P X = conePlus P X := hc.2.2.1.symm.trans h
    calc conePlus P X + conePlus P X
        = conePlus P X + -conePlus P X := by rw [hneg]
      _ = 0 := add_neg_cancel _
  · have hneg : -coneMinus P X = coneMinus P X := hc.2.2.2.symm.trans h
    calc coneMinus P X + coneMinus P X
        = coneMinus P X + -coneMinus P X := by rw [hneg]
      _ = 0 := add_neg_cancel _

/-- **Row 2 (Multiplicative Sheet Swap `μ`)**: exchanges the two even body corners
and exchanges the two odd chiral soul corners `conePlus ↔ coneMinus`. -/
theorem multSheetSwap_corners {P : B} (μ : B → B)
    (hμ_mul : ∀ a b : B, μ (a * b) = μ a * μ b)
    (hμP : μ P = 1 - P) (hμQ : μ (1 - P) = P) (X : B) :
    μ (peirce11 P X) = peirce00 P (μ X) ∧
    μ (peirce00 P X) = peirce11 P (μ X) ∧
    μ (conePlus P X) = coneMinus P (μ X) ∧
    μ (coneMinus P X) = conePlus P (μ X) := by
  dsimp [peirce11, peirce00, conePlus, coneMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hμ_mul, hμ_mul, hμP]
  · rw [hμ_mul, hμ_mul, hμQ]
  · rw [hμ_mul, hμ_mul, hμP, hμQ]
  · rw [hμ_mul, hμ_mul, hμQ, hμP]

/-- **Row 2 Fermion-Vanishing Law**: any single-corner element fixed by a multiplicative
sheet swap `μ` vanishes identically (no 2-torsion hypothesis needed). -/
theorem multSheetSwap_singleCorner_fixed_zero {P : B} (hP : P * P = P)
    (μ : B → B) (hμ_mul : ∀ a b : B, μ (a * b) = μ a * μ b)
    (hμP : μ P = 1 - P) (hμQ : μ (1 - P) = P) (X : B) :
    (μ (conePlus P X) = conePlus P X → conePlus P X = 0) ∧
    (μ (coneMinus P X) = coneMinus P X → coneMinus P X = 0) := by
  have hc := multSheetSwap_corners μ hμ_mul hμP hμQ X
  refine ⟨?_, ?_⟩
  · intro hFix
    calc conePlus P X = P * conePlus P X := (P_mul_conePlus hP X).symm
      _ = P * μ (conePlus P X) := by rw [hFix]
      _ = P * coneMinus P (μ X) := by rw [hc.2.2.1]
      _ = 0 := P_mul_coneMinus hP (μ X)
  · intro hFix
    calc coneMinus P X = coneMinus P X * P := (coneMinus_mul_P hP X).symm
      _ = μ (coneMinus P X) * P := by rw [hFix]
      _ = conePlus P (μ X) * P := by rw [hc.2.2.2]
      _ = 0 := conePlus_mul_P hP (μ X)

/-- **Row 3 (Star Involution `*`)**: self-adjoint idempotent preserves the even corners
`peirce11`, `peirce00` and swaps `conePlus ↔ coneMinus`. -/
theorem star_peirce11 [StarRing B] {P : B} (hPs : star P = P) (X : B) :
    star (peirce11 P X) = peirce11 P (star X) := by
  simp only [peirce11, star_mul, hPs, mul_assoc]

theorem star_peirce00 [StarRing B] {P : B} (hPs : star P = P) (X : B) :
    star (peirce00 P X) = peirce00 P (star X) := by
  simp only [peirce00, star_mul, star_sub, star_one, hPs, mul_assoc]

/-- **Row 3 Single-Corner Vanishing**: a self-adjoint element living in a single
chiral corner vanishes (`B₁₀ ∩ B₀₁ = {0}`). -/
theorem selfAdjoint_singleCorner_eq_zero [StarRing B] {P : B}
    (hPs : star P = P) (hP : P * P = P) (X : B) (hSA : star X = X) :
    (X = conePlus P X → X = 0) ∧ (X = coneMinus P X → X = 0) := by
  refine ⟨?_, ?_⟩
  · intro hPlus
    have hMinus : X = coneMinus P X := by
      calc X = star X := hSA.symm
        _ = star (conePlus P X) := congrArg star hPlus
        _ = coneMinus P (star X) := star_conePlus hPs X
        _ = coneMinus P X := by rw [hSA]
    calc X = conePlus P X := hPlus
      _ = P * conePlus P X := (P_mul_conePlus hP X).symm
      _ = P * X := by conv_rhs => rw [hPlus]
      _ = P * coneMinus P X := by rw [← hMinus]
      _ = 0 := P_mul_coneMinus hP X
  · intro hMinus
    have hPlus : X = conePlus P X := by
      calc X = star X := hSA.symm
        _ = star (coneMinus P X) := congrArg star hMinus
        _ = conePlus P (star X) := star_coneMinus hPs X
        _ = conePlus P X := by rw [hSA]
    calc X = coneMinus P X := hMinus
      _ = coneMinus P X * P := (coneMinus_mul_P hP X).symm
      _ = X * P := by conv_rhs => rw [hMinus]
      _ = conePlus P X * P := by rw [← hPlus]
      _ = 0 := conePlus_mul_P hP X

/-- **Row 3 Body + Paired Majorana-Soul Split (Fermion-Doubling Law)**:
every self-adjoint element `X = X⋆` forces `coneMinus P X = (conePlus P X)⋆` and splits into
an even self-adjoint body `evenGrade P X` plus a paired Majorana soul `N₊ + N₊⋆`. -/
theorem selfAdjoint_body_majorana_soul_split [StarRing B] {P : B}
    (hPs : star P = P) (X : B) (hSA : star X = X) :
    coneMinus P X = star (conePlus P X) ∧
    star (evenGrade P X) = evenGrade P X ∧
    star (conePlus P X + star (conePlus P X)) = conePlus P X + star (conePlus P X) ∧
    X = evenGrade P X + (conePlus P X + star (conePlus P X)) := by
  have hMinus : coneMinus P X = star (conePlus P X) := by
    calc coneMinus P X = coneMinus P (star X) := by rw [hSA]
      _ = star (conePlus P X) := (star_conePlus hPs X).symm
  refine ⟨hMinus, ?_, ?_, ?_⟩
  · dsimp [evenGrade]
    simp only [star_add, star_mul, star_sub, star_one, hPs, hSA, mul_assoc]
  · simp only [star_add, star_star, add_comm]
  · have h1 : X = (P + (1 - P)) * X * (P + (1 - P)) := by
      rw [add_sub_cancel, one_mul, mul_one]
    conv_lhs => rw [h1]
    rw [← hMinus]
    dsimp [evenGrade, conePlus, coneMinus]
    noncomm_ring

/-- **Row 4 (Anti-Multiplicative Sheet Swap `τ`)**: swaps the even body corners `peirce11 ↔ peirce00`
while double-reversal cancellation **preserves** each odd chiral soul corner `conePlus` and `coneMinus`. -/
theorem antiMultSheetSwap_corners {P : B} (τ : B → B)
    (hτ_mul : ∀ a b : B, τ (a * b) = τ b * τ a)
    (hτP : τ P = 1 - P) (hτQ : τ (1 - P) = P) (X : B) :
    τ (peirce11 P X) = peirce00 P (τ X) ∧
    τ (peirce00 P X) = peirce11 P (τ X) ∧
    τ (conePlus P X) = conePlus P (τ X) ∧
    τ (coneMinus P X) = coneMinus P (τ X) := by
  dsimp [peirce11, peirce00, conePlus, coneMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hτ_mul, hτ_mul, hτP, ← mul_assoc]
  · rw [hτ_mul, hτ_mul, hτQ, ← mul_assoc]
  · rw [hτ_mul, hτ_mul, hτQ, hτP, ← mul_assoc]
  · rw [hτ_mul, hτ_mul, hτP, hτQ, ← mul_assoc]

/-- **Multiplicative/anti-multiplicative sheet-swap obstruction**: if a multiplicative
sheet swap and an anti-multiplicative sheet swap agree on an element in either single
off-diagonal Peirce corner, that corner element is zero. The two maps send the same
corner into opposite corners; injectivity and zero preservation of the multiplicative
map then force the original element to vanish. -/
theorem multAntiMultSheetSwap_fixed_singleCorner_eq_zero {P : B}
    (hP : P * P = P) (φ τ : B → B)
    (hφ_mul : ∀ a b : B, φ (a * b) = φ a * φ b)
    (hφ_zero : φ 0 = 0) (hφ_inj : Function.Injective φ)
    (hφP : φ P = 1 - P) (hφQ : φ (1 - P) = P)
    (hτ_mul : ∀ a b : B, τ (a * b) = τ b * τ a)
    (hτP : τ P = 1 - P) (hτQ : τ (1 - P) = P) (X : B) :
    (φ (conePlus P X) = τ (conePlus P X) → conePlus P X = 0) ∧
    (φ (coneMinus P X) = τ (coneMinus P X) → coneMinus P X = 0) := by
  have hφCorners := multSheetSwap_corners φ hφ_mul hφP hφQ X
  have hτCorners := antiMultSheetSwap_corners τ hτ_mul hτP hτQ X
  refine ⟨?_, ?_⟩
  · intro hAgree
    have hCross : coneMinus P (φ X) = conePlus P (τ X) := by
      calc
        coneMinus P (φ X) = φ (conePlus P X) := hφCorners.2.2.1.symm
        _ = τ (conePlus P X) := hAgree
        _ = conePlus P (τ X) := hτCorners.2.2.1
    have hProj := congrArg (fun z : B => P * z) hCross
    rw [P_mul_coneMinus hP, P_mul_conePlus hP] at hProj
    have hImageZero : φ (conePlus P X) = 0 := by
      calc
        φ (conePlus P X) = coneMinus P (φ X) := hφCorners.2.2.1
        _ = conePlus P (τ X) := hCross
        _ = 0 := hProj.symm
    apply hφ_inj
    simpa [hφ_zero] using hImageZero
  · intro hAgree
    have hCross : conePlus P (φ X) = coneMinus P (τ X) := by
      calc
        conePlus P (φ X) = φ (coneMinus P X) := hφCorners.2.2.2.symm
        _ = τ (coneMinus P X) := hAgree
        _ = coneMinus P (τ X) := hτCorners.2.2.2
    have hProj := congrArg (fun z : B => z * P) hCross
    rw [conePlus_mul_P hP, coneMinus_mul_P hP] at hProj
    have hImageZero : φ (coneMinus P X) = 0 := by
      calc
        φ (coneMinus P X) = conePlus P (φ X) := hφCorners.2.2.2
        _ = coneMinus P (τ X) := hCross
        _ = 0 := hProj.symm
    apply hφ_inj
    simpa [hφ_zero] using hImageZero

/-- **Row 4 × Row 3 = Row 2 Coupling**: composing `*` (Row 3) with an anti-multiplicative
sheet swap `τ` (Row 4) yields a multiplicative sheet swap `* ∘ τ` (Row 2) that exchanges `conePlus ↔ coneMinus`
and forces any fixed single-corner element to vanish. -/
theorem star_comp_antiMultSheetSwap_is_multSheetSwap [StarRing B] {P : B}
    (hPs : star P = P) (hP : P * P = P) (τ : B → B)
    (hτ_mul : ∀ a b : B, τ (a * b) = τ b * τ a)
    (hτP : τ P = 1 - P) (hτQ : τ (1 - P) = P) :
    (∀ a b : B, star (τ (a * b)) = star (τ a) * star (τ b)) ∧
    star (τ P) = 1 - P ∧
    star (τ (1 - P)) = P ∧
    (∀ X : B, star (τ (conePlus P X)) = coneMinus P (star (τ X))) ∧
    (∀ X : B, star (τ (coneMinus P X)) = conePlus P (star (τ X))) ∧
    (∀ X : B, star (τ (conePlus P X)) = conePlus P X → conePlus P X = 0) := by
  have hmul : ∀ a b : B, star (τ (a * b)) = star (τ a) * star (τ b) := fun a b => by
    rw [hτ_mul, star_mul]
  have hP' : star (τ P) = 1 - P := by
    rw [hτP, star_sub, star_one, hPs]
  have hQ' : star (τ (1 - P)) = P := by
    rw [hτQ, hPs]
  refine ⟨hmul, hP', hQ', ?_, ?_, ?_⟩
  · intro X
    exact (multSheetSwap_corners (fun z => star (τ z)) hmul hP' hQ' X).2.2.1
  · intro X
    exact (multSheetSwap_corners (fun z => star (τ z)) hmul hP' hQ' X).2.2.2
  · intro X
    exact (multSheetSwap_singleCorner_fixed_zero hP (fun z => star (τ z)) hmul hP' hQ' X).1

/-- Concrete algebraic realization of Row 4 (`τ(A) = U A⋆ U`) from a self-adjoint involution `U² = 1`
conjugating `U P U = 1 - P`. -/
theorem unitStarConjugation_is_row4_antiMultSheetSwap [StarRing B] {P : B}
    (hPs : star P = P) (U : B) (hU2 : U * U = 1) (hUs : star U = U)
    (hUP : U * P * U = 1 - P) :
    (∀ A : B, U * star (U * star A * U) * U = A) ∧
    (∀ A C : B, U * star (A * C) * U = (U * star C * U) * (U * star A * U)) ∧
    U * star P * U = 1 - P ∧
    U * star (1 - P) * U = P ∧
    (∀ X : B, U * star (conePlus P X) * U = conePlus P (U * star X * U)) ∧
    (∀ X : B, U * star (coneMinus P X) * U = coneMinus P (U * star X * U)) := by
  have hmul : ∀ A C : B, U * star (A * C) * U = (U * star C * U) * (U * star A * U) := fun A C => by
    calc U * star (A * C) * U
        = U * (star C * 1 * star A) * U := by rw [star_mul, mul_one]
      _ = U * (star C * (U * U) * star A) * U := by rw [hU2]
      _ = (U * star C * U) * (U * star A * U) := by noncomm_ring
  have hτP : U * star P * U = 1 - P := by rw [hPs, hUP]
  have hτQ : U * star (1 - P) * U = P := by
    rw [star_sub, star_one, hPs]
    calc U * (1 - P) * U = U * 1 * U - U * P * U := by noncomm_ring
      _ = U * U - (1 - P) := by rw [mul_one, hUP]
      _ = 1 - (1 - P) := by rw [hU2]
      _ = P := by abel
  refine ⟨?_, hmul, hτP, hτQ, ?_, ?_⟩
  · intro A
    calc U * star (U * star A * U) * U
        = U * (star U * star (star A) * star U) * U := by
          simp only [star_mul, mul_assoc]
      _ = (U * U) * A * (U * U) := by
          rw [hUs, star_star]; noncomm_ring
      _ = A := by rw [hU2, one_mul, mul_one]
  · intro X
    exact (antiMultSheetSwap_corners (fun z => U * star z * U) hmul hτP hτQ X).2.2.1
  · intro X
    exact (antiMultSheetSwap_corners (fun z => U * star z * U) hmul hτP hτQ X).2.2.2

end PeirceCornerInvolutionTable

end InfoGeometry.OperatorAlgebra.PeirceSpine
