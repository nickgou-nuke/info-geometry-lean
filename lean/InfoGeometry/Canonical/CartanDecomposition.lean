import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical.CartanDecomposition

open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin

variable {R : Type*} [Ring R] [StarRing R]

/-!
# Information Cartan Decomposition

This module formalizes the splitting of belief updates into symmetric (compact)
and antisymmetric (non-compact) generators, driven by the discrepancy between
geometric and spectral information.
-/

/-- 
The Information Cartan Triple.
Pairs a degenerate information operator with its two canonical regularizations.
-/
structure InformationCartanTriple (R : Type*) [Ring R] [StarRing R] where
  A    : R
  A_D  : R
  A_MP : R

namespace InformationCartanTriple

variable (T : InformationCartanTriple R)

/-! ### 1. Chiral Operators (Gradings) -/

/-- 
The Geometric Chiral Operator (Geometric Grading).
Γ_G = P_R - P_L = A*A⁺ - A⁺*A.
Captures the 'Metric Orientation' of the belief manifold.
-/
def GammaG : R := 
  (IsMoorePenroseInverse.rightProjector T.A T.A_MP) - (IsMoorePenroseInverse.leftProjector T.A T.A_MP)

/-- 
The Spectral Chiral Operator (Spectral Grading).
Γ_S = 2*P_D - 1.
Captures the 'Algebraic Orientation' of the belief manifold.
-/
def GammaS : R := 
  2 * (IsDrazinInverse.projection T.A T.A_D) - 1

/-- The Drazin spectral projector. -/
def spectralProjector : R :=
  IsDrazinInverse.projection T.A T.A_D

/-- The complementary Drazin spectral projector. -/
def spectralComplement : R :=
  IsDrazinInverse.complementaryProjection T.A T.A_D

/-- 
Theorem: The commutator of the Geometric and Spectral Gradings is 
directly proportional to the Chiral Anomaly.
[Γ_G, Γ_S] = 2 [Γ_G, P_D].
-/
theorem grading_commutator_anomaly :
    T.GammaG * T.GammaS - T.GammaS * T.GammaG = 2 * (T.GammaG * (IsDrazinInverse.projection T.A T.A_D) - (IsDrazinInverse.projection T.A T.A_D) * T.GammaG) := by
  unfold GammaS
  noncomm_ring

/--
The spectral grading is an involution whenever the Drazin projector exists.
This is the robust Cartan seed coming from the idempotent projector
`P_D = A * A_D`.
-/
theorem GammaS_sq_eq_one
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.GammaS * T.GammaS = (1 : R) := by
  let P := IsDrazinInverse.projection T.A T.A_D
  have hP :
      P * P = P :=
    IsDrazinInverse.projection_is_idempotent hD
  change (2 * P - 1) * (2 * P - 1) = (1 : R)
  noncomm_ring [hP]

/-- The spectral grading is `+1` on the Drazin spectral projector. -/
theorem GammaS_mul_spectralProjector
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.GammaS * T.spectralProjector = T.spectralProjector := by
  let P := IsDrazinInverse.projection T.A T.A_D
  have hP :
      P * P = P :=
    IsDrazinInverse.projection_is_idempotent hD
  change (2 * P - 1) * P = P
  noncomm_ring [hP]

/-- The Drazin spectral projector is a `+1` eigen-operator for the spectral grading on the right. -/
theorem spectralProjector_mul_GammaS
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.spectralProjector * T.GammaS = T.spectralProjector := by
  let P := IsDrazinInverse.projection T.A T.A_D
  have hP :
      P * P = P :=
    IsDrazinInverse.projection_is_idempotent hD
  change P * (2 * P - 1) = P
  noncomm_ring [hP]

/-- The spectral grading is `-1` on the complementary Drazin projector. -/
theorem GammaS_mul_spectralComplement
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.GammaS * T.spectralComplement = -T.spectralComplement := by
  let P := IsDrazinInverse.projection T.A T.A_D
  have hP :
      P * P = P :=
    IsDrazinInverse.projection_is_idempotent hD
  change (2 * P - 1) * (1 - P) = -(1 - P)
  noncomm_ring [hP]

/-- The complementary Drazin projector is a `-1` eigen-operator for the spectral grading on the right. -/
theorem spectralComplement_mul_GammaS
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.spectralComplement * T.GammaS = -T.spectralComplement := by
  let P := IsDrazinInverse.projection T.A T.A_D
  have hP :
      P * P = P :=
    IsDrazinInverse.projection_is_idempotent hD
  change (1 - P) * (2 * P - 1) = -(1 - P)
  noncomm_ring [hP]

/-- Spectral Cartan involution induced by the Drazin grading. -/
def thetaS : R → R := fun X => T.GammaS * X * T.GammaS

/--
The spectral Cartan involution squares to the identity once the Drazin grading
is involutive.
-/
theorem thetaS_involutive
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (X : R) :
    T.thetaS (T.thetaS X) = X := by
  unfold thetaS
  calc
    T.GammaS * (T.GammaS * X * T.GammaS) * T.GammaS
        = (T.GammaS * T.GammaS) * X * (T.GammaS * T.GammaS) := by
            noncomm_ring
    _ = (1 : R) * X * (1 : R) := by
          simp [T.GammaS_sq_eq_one hD]
    _ = X := by simp

/-- The spectral Cartan involution fixes the Drazin spectral projector. -/
theorem thetaS_spectralProjector
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.thetaS T.spectralProjector = T.spectralProjector := by
  unfold thetaS
  rw [T.GammaS_mul_spectralProjector hD, T.spectralProjector_mul_GammaS hD]

/-- The spectral Cartan involution fixes the complementary Drazin projector. -/
theorem thetaS_spectralComplement
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.thetaS T.spectralComplement = T.spectralComplement := by
  unfold thetaS
  rw [T.GammaS_mul_spectralComplement hD]
  rw [neg_mul, T.spectralComplement_mul_GammaS hD]
  simp

/-! ### 2. The Cartan Splitting 𝔨 ⊕ 𝔭 -/

/-- Spectral compact sector: fixed points of the spectral Cartan involution. -/
def IsSpectralCompact (X : R) : Prop := T.thetaS X = X

/-- Spectral noncompact sector: `-1` eigenspace of the spectral Cartan involution. -/
def IsSpectralNonCompact (X : R) : Prop := T.thetaS X = -X

/-- Spectral Lie commutator. -/
def spectralCommutator (X Y : R) : R := X * Y - Y * X

/--
The fixed-point condition for the spectral Cartan involution is exactly
commutation with the spectral grading.
-/
theorem isSpectralCompact_iff_commute
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X : R} :
    T.IsSpectralCompact X ↔ X * T.GammaS = T.GammaS * X := by
  constructor
  · intro hFix
    unfold IsSpectralCompact thetaS at hFix
    calc
      X * T.GammaS = ((1 : R) * X) * T.GammaS := by simp
      _ = ((T.GammaS * T.GammaS) * X) * T.GammaS := by
            rw [T.GammaS_sq_eq_one hD]
      _ = T.GammaS * (T.GammaS * X * T.GammaS) := by
            simp [mul_assoc]
      _ = T.GammaS * X := by rw [hFix]
  · intro hComm
    unfold IsSpectralCompact thetaS
    calc
      T.GammaS * X * T.GammaS = X * (T.GammaS * T.GammaS) := by
        rw [← mul_assoc, hComm, mul_assoc]
      _ = X := by simp [T.GammaS_sq_eq_one hD]

/--
The `-1` eigenspace condition for the spectral Cartan involution is exactly
anticommutation with the spectral grading.
-/
theorem isSpectralNonCompact_iff_anticommute
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X : R} :
    T.IsSpectralNonCompact X ↔ X * T.GammaS = -(T.GammaS * X) := by
  constructor
  · intro hNeg
    unfold IsSpectralNonCompact thetaS at hNeg
    calc
      X * T.GammaS = ((1 : R) * X) * T.GammaS := by simp
      _ = ((T.GammaS * T.GammaS) * X) * T.GammaS := by
            rw [T.GammaS_sq_eq_one hD]
      _ = T.GammaS * (T.GammaS * X * T.GammaS) := by
            simp [mul_assoc]
      _ = T.GammaS * (-X) := by rw [hNeg]
      _ = -(T.GammaS * X) := by simp
  · intro hAnti
    unfold IsSpectralNonCompact thetaS
    calc
      T.GammaS * X * T.GammaS = T.GammaS * (X * T.GammaS) := by simp [mul_assoc]
      _ = T.GammaS * (-(T.GammaS * X)) := by rw [hAnti]
      _ = -((T.GammaS * T.GammaS) * X) := by simp [mul_assoc]
      _ = -X := by simp [T.GammaS_sq_eq_one hD]

/-- The Drazin spectral projector lies in the spectral compact sector. -/
theorem spectralProjector_isSpectralCompact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.IsSpectralCompact T.spectralProjector := by
  exact T.thetaS_spectralProjector hD

/-- The complementary Drazin spectral projector also lies in the spectral compact sector. -/
theorem spectralComplement_isSpectralCompact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.IsSpectralCompact T.spectralComplement := by
  exact T.thetaS_spectralComplement hD

/-- The spectral compact sector is closed under the Lie commutator. -/
theorem spectralCommutator_mem_compact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X Y : R}
    (hX : T.IsSpectralCompact X)
    (hY : T.IsSpectralCompact Y) :
    T.IsSpectralCompact (spectralCommutator X Y) := by
  rw [T.isSpectralCompact_iff_commute hD] at hX hY ⊢
  unfold spectralCommutator
  calc
    (X * Y - Y * X) * T.GammaS
        = X * (Y * T.GammaS) - Y * (X * T.GammaS) := by
            simp [sub_mul, mul_assoc]
    _ = X * (T.GammaS * Y) - Y * (T.GammaS * X) := by rw [hY, hX]
    _ = (T.GammaS * X) * Y - (T.GammaS * Y) * X := by
          rw [← mul_assoc, ← mul_assoc, hX, hY]
    _ = T.GammaS * (X * Y) - T.GammaS * (Y * X) := by
          simp [mul_assoc]
    _ = T.GammaS * (X * Y - Y * X) := by rw [mul_sub]

/-- The mixed spectral commutator lands in the noncompact sector. -/
theorem spectralCommutator_compact_noncompact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X Y : R}
    (hX : T.IsSpectralCompact X)
    (hY : T.IsSpectralNonCompact Y) :
    T.IsSpectralNonCompact (spectralCommutator X Y) := by
  rw [T.isSpectralCompact_iff_commute hD] at hX
  rw [T.isSpectralNonCompact_iff_anticommute hD] at hY ⊢
  unfold spectralCommutator
  calc
    (X * Y - Y * X) * T.GammaS
        = X * (Y * T.GammaS) - Y * (X * T.GammaS) := by
            simp [sub_mul, mul_assoc]
    _ = X * (-(T.GammaS * Y)) - Y * (T.GammaS * X) := by rw [hY, hX]
    _ = -((X * T.GammaS) * Y) - (Y * T.GammaS) * X := by
          simp [mul_assoc]
    _ = -((T.GammaS * X) * Y) - (-(T.GammaS * Y)) * X := by rw [hX, hY]
    _ = -(T.GammaS * (X * Y)) + T.GammaS * (Y * X) := by
          simp [mul_assoc]
    _ = -(T.GammaS * (X * Y - Y * X)) := by
          rw [mul_sub]
          abel_nf

/-- The noncompact sector brackets back into the compact sector. -/
theorem spectralCommutator_mem_compact_of_noncompact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X Y : R}
    (hX : T.IsSpectralNonCompact X)
    (hY : T.IsSpectralNonCompact Y) :
    T.IsSpectralCompact (spectralCommutator X Y) := by
  rw [T.isSpectralNonCompact_iff_anticommute hD] at hX hY
  rw [T.isSpectralCompact_iff_commute hD]
  unfold spectralCommutator
  calc
    (X * Y - Y * X) * T.GammaS
        = X * (Y * T.GammaS) - Y * (X * T.GammaS) := by
            simp [sub_mul, mul_assoc]
    _ = X * (-(T.GammaS * Y)) - Y * (-(T.GammaS * X)) := by rw [hY, hX]
    _ = -((X * T.GammaS) * Y) + (Y * T.GammaS) * X := by
          simp [mul_assoc]
    _ = -((-(T.GammaS * X)) * Y) + (-(T.GammaS * Y)) * X := by rw [hX, hY]
    _ = T.GammaS * (X * Y) - T.GammaS * (Y * X) := by
          simp [mul_assoc, sub_eq_add_neg]
    _ = T.GammaS * (X * Y - Y * X) := by rw [mul_sub]

/-- 
The Compact (Rotational) Component.
Belief updates X that commute with the Geometric Grading Γ_G.
These preserve the 'Information Chirality'.
-/
def IsCompact (X : R) : Prop := X * T.GammaG = T.GammaG * X

/-- 
The Non-Compact (Boost) Component.
Belief updates X that anti-commute with the Geometric Grading Γ_G.
These drive the 'Information Scale' flow.
-/
def IsNonCompact (X : R) : Prop := X * T.GammaG = - (T.GammaG * X)

/-- 
Theorem: In a Normal belief manifold (ε = 0), the Spectral Projector 
is purely compact.
-/
theorem spectral_proj_is_compact_of_normal
    (h_gamma : T.GammaG = 0) :
    IsCompact T (IsDrazinInverse.projection T.A T.A_D) := by
  simp [IsCompact, h_gamma]

end InformationCartanTriple

namespace InformationCartanTriple

section Exponential

variable {S : Type*} [NormedRing S] [StarRing S]
variable [NormedAlgebra ℚ S] [NormedAlgebra ℝ S] [CompleteSpace S]
variable [IsTopologicalRing S] [SMulCommClass ℝ S S] [IsScalarTower ℝ S S]

variable (T : InformationCartanTriple S)

omit [StarRing S] [NormedAlgebra ℚ S] [CompleteSpace S] [IsTopologicalRing S] in
private lemma smul_pow_even_of_sq_eq_one
    (G : S) (hSq : G * G = (1 : S)) (t : ℝ) :
    ∀ n : ℕ, (t • G) ^ (2 * n) = (t ^ (2 * n)) • (1 : S)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = (t ^ 2) • (1 : S) := by
        rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSq]
        simp [pow_two]
      calc
        (t • G) ^ (2 * (n + 1))
            = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = ((t ^ (2 * n)) • (1 : S)) * ((t ^ 2) • (1 : S)) := by
              rw [smul_pow_even_of_sq_eq_one G hSq t n, hpow2]
        _ = (t ^ (2 * (n + 1))) • (1 : S) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
              rw [← pow_add]
              simp [show 2 * (n + 1) = 2 * n + 2 by omega]

omit [StarRing S] [NormedAlgebra ℚ S] [CompleteSpace S] [IsTopologicalRing S] in
private lemma smul_pow_odd_of_sq_eq_one
    (G : S) (hSq : G * G = (1 : S)) (t : ℝ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) = (t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1)
        = (t • G) ^ (2 * n) * (t • G) := by
            rw [pow_succ]
    _ = ((t ^ (2 * n)) • (1 : S)) * (t • G) := by
          rw [smul_pow_even_of_sq_eq_one G hSq t n]
    _ = (t ^ (2 * n + 1)) • G := by
          rw [smul_mul_assoc, one_mul, smul_smul]
          simp [pow_succ]

omit [StarRing S] [NormedAlgebra ℚ S] [CompleteSpace S] in
/-- Closed form for the exponential of an involution in the operator algebra. -/
theorem exp_eq_cosh_add_sinh_of_sq_eq_one
    {G : S} (hSq : G * G = (1 : S)) (t : ℝ) :
    NormedSpace.exp (t • G) = Real.cosh t • (1 : S) + Real.sinh t • G := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum :
      HasSum
        (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (t • G) ^ n)
        (((Real.cosh t : ℝ) • (1 : S)) + ((Real.sinh t : ℝ) • G)) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Real.hasSum_cosh t).smul_const (1 : S) using 1
      ext n
      rw [smul_pow_even_of_sq_eq_one G hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
    · convert (Real.hasSum_sinh t).smul_const G using 1
      ext n
      rw [smul_pow_odd_of_sq_eq_one G hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
  exact hsum.tsum_eq

/-- Spectral compact exponential flow generated by an operator. -/
noncomputable def spectralCompactFlow (T : InformationCartanTriple S) (X : S) (t : ℝ) : S :=
  let _ := T.A
  NormedSpace.exp (t • X)

/-- Adjoint transport by the spectral compact exponential flow. -/
noncomputable def spectralAdjointFlow (X : S) (t : ℝ) (Y : S) : S :=
  T.spectralCompactFlow X t * Y * T.spectralCompactFlow X (-t)

/-- The distinguished spectral one-parameter flow generated by `Γ_S`. -/
noncomputable def spectralGradingFlow (t : ℝ) : S :=
  T.spectralCompactFlow T.GammaS t

/-- The exponential flow of any generator satisfies the additive one-parameter law. -/
theorem spectralCompactFlow_add (X : S) (s t : ℝ) :
    T.spectralCompactFlow X (s + t) =
      T.spectralCompactFlow X s * T.spectralCompactFlow X t := by
  have hComm : Commute (s • X) (t • X) := by
    exact ((Commute.refl X).smul_left s).smul_right t
  simpa [spectralCompactFlow, add_smul] using
    (NormedSpace.exp_add_of_commute (𝔸 := S) hComm)

/-- The grading flow is a one-parameter exponential subgroup. -/
theorem spectralGradingFlow_add (s t : ℝ) :
    T.spectralGradingFlow (s + t) =
      T.spectralGradingFlow s * T.spectralGradingFlow t := by
  simpa [spectralGradingFlow] using T.spectralCompactFlow_add T.GammaS s t

omit [NormedAlgebra ℚ S] [CompleteSpace S] [SMulCommClass ℝ S S] [IsScalarTower ℝ S S] in
/-- The grading flow starts at the identity. -/
theorem spectralGradingFlow_zero :
    T.spectralGradingFlow 0 = (1 : S) := by
  simp [spectralGradingFlow, spectralCompactFlow]

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/-- Closed form for the spectral grading flow generated by the involution `Γ_S`. -/
theorem spectralGradingFlow_eq_cosh_add_sinh_GammaS
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (t : ℝ) :
    T.spectralGradingFlow t = Real.cosh t • (1 : S) + Real.sinh t • T.GammaS := by
  unfold spectralGradingFlow spectralCompactFlow
  exact exp_eq_cosh_add_sinh_of_sq_eq_one (G := T.GammaS) (T.GammaS_sq_eq_one hD) t

omit [NormedAlgebra ℚ S] [NormedAlgebra ℝ S] [CompleteSpace S]
  [IsTopologicalRing S] [SMulCommClass ℝ S S] [IsScalarTower ℝ S S] in
/-- The spectral grading itself lies in the compact Cartan sector. -/
theorem GammaS_isSpectralCompact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k) :
    T.IsSpectralCompact T.GammaS := by
  rw [T.isSpectralCompact_iff_commute hD]

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/--
The spectral compact sector is closed under the exponential map of a compact
generator.
-/
theorem spectralCompactFlow_mem_compact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X : S}
    (hX : T.IsSpectralCompact X)
    (t : ℝ) :
    T.IsSpectralCompact (T.spectralCompactFlow X t) := by
  rw [T.isSpectralCompact_iff_commute hD] at hX ⊢
  have hCommScaled : Commute (t • X) T.GammaS := by
    exact (show Commute X T.GammaS from hX).smul_left t
  simpa [spectralCompactFlow] using hCommScaled.exp_left.eq

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/-- The grading flow is spectral-compact for every time parameter. -/
theorem spectralGradingFlow_mem_compact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (t : ℝ) :
    T.IsSpectralCompact (T.spectralGradingFlow t) := by
  simpa [spectralGradingFlow] using
    T.spectralCompactFlow_mem_compact hD (X := T.GammaS) (T.GammaS_isSpectralCompact hD) t

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/-- Any operator commuting with `Γ_S` commutes with the full grading flow. -/
theorem commute_spectralGradingFlow_of_commute_GammaS
    {Y : S}
    (hY : Commute Y T.GammaS)
    (t : ℝ) :
    Commute Y (T.spectralGradingFlow t) := by
  simpa [spectralGradingFlow, spectralCompactFlow] using
    (hY.smul_right t).exp_right

/-- Any operator commuting with `Γ_S` is fixed by the grading adjoint flow. -/
theorem spectralAdjointFlow_eq_self_of_commute_GammaS
    {Y : S}
    (hY : Commute Y T.GammaS)
    (t : ℝ) :
    T.spectralAdjointFlow T.GammaS t Y = Y := by
  unfold spectralAdjointFlow
  have hComm :
      Commute Y (T.spectralCompactFlow T.GammaS t) := by
    simpa [spectralGradingFlow] using
      T.commute_spectralGradingFlow_of_commute_GammaS hY t
  have hProd :
      T.spectralCompactFlow T.GammaS t * T.spectralCompactFlow T.GammaS (-t)
        = T.spectralGradingFlow (t + (-t)) := by
    simpa [spectralGradingFlow] using
      (T.spectralGradingFlow_add t (-t)).symm
  calc
    T.spectralCompactFlow T.GammaS t * Y * T.spectralCompactFlow T.GammaS (-t)
        = Y * (T.spectralCompactFlow T.GammaS t * T.spectralCompactFlow T.GammaS (-t)) := by
            rw [← hComm.eq]
            simp [mul_assoc]
    _ = Y * T.spectralGradingFlow (t + (-t)) := by
          rw [hProd]
    _ = Y := by
          simp [spectralGradingFlow_zero]

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/-- The Drazin spectral projector commutes with the grading flow. -/
theorem spectralProjector_commutes_spectralGradingFlow
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (t : ℝ) :
    Commute T.spectralProjector (T.spectralGradingFlow t) := by
  have hPΓ : Commute T.spectralProjector T.GammaS := by
    change T.spectralProjector * T.GammaS = T.GammaS * T.spectralProjector
    rw [T.spectralProjector_mul_GammaS hD, T.GammaS_mul_spectralProjector hD]
  simpa [spectralGradingFlow, spectralCompactFlow] using
    (hPΓ.smul_right t).exp_right

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/-- The complementary Drazin projector also commutes with the grading flow. -/
theorem spectralComplement_commutes_spectralGradingFlow
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (t : ℝ) :
    Commute T.spectralComplement (T.spectralGradingFlow t) := by
  have hQΓ : Commute T.spectralComplement T.GammaS := by
    change T.spectralComplement * T.GammaS = T.GammaS * T.spectralComplement
    rw [T.spectralComplement_mul_GammaS hD, T.GammaS_mul_spectralComplement hD]
  simpa [spectralGradingFlow, spectralCompactFlow] using
    (hQΓ.smul_right t).exp_right

/-- The grading adjoint flow fixes the Drazin spectral projector. -/
theorem spectralProjector_fixed_under_spectralGradingFlow
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (t : ℝ) :
    T.spectralAdjointFlow T.GammaS t T.spectralProjector = T.spectralProjector := by
  have hPΓ : Commute T.spectralProjector T.GammaS := by
    change T.spectralProjector * T.GammaS = T.GammaS * T.spectralProjector
    rw [T.spectralProjector_mul_GammaS hD, T.GammaS_mul_spectralProjector hD]
  simpa using T.spectralAdjointFlow_eq_self_of_commute_GammaS hPΓ t

/-- The grading adjoint flow fixes the complementary Drazin projector. -/
theorem spectralComplement_fixed_under_spectralGradingFlow
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    (t : ℝ) :
    T.spectralAdjointFlow T.GammaS t T.spectralComplement = T.spectralComplement := by
  have hQΓ : Commute T.spectralComplement T.GammaS := by
    change T.spectralComplement * T.GammaS = T.GammaS * T.spectralComplement
    rw [T.spectralComplement_mul_GammaS hD, T.GammaS_mul_spectralComplement hD]
  simpa using T.spectralAdjointFlow_eq_self_of_commute_GammaS hQΓ t

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/--
Adjoint transport by a spectral compact flow preserves the compact sector.
-/
theorem spectralAdjointFlow_mem_compact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X Y : S}
    (hX : T.IsSpectralCompact X)
    (hY : T.IsSpectralCompact Y)
    (t : ℝ) :
    T.IsSpectralCompact (T.spectralAdjointFlow X t Y) := by
  rw [T.isSpectralCompact_iff_commute hD] at hX hY ⊢
  unfold spectralAdjointFlow
  have hExp :
      Commute (T.spectralCompactFlow X t) T.GammaS := by
    have hCommScaled : Commute (t • X) T.GammaS := by
      exact (show Commute X T.GammaS from hX).smul_left t
    simpa [spectralCompactFlow] using hCommScaled.exp_left
  have hExpNeg :
      Commute (T.spectralCompactFlow X (-t)) T.GammaS := by
    have hCommScaled : Commute ((-t) • X) T.GammaS := by
      exact (show Commute X T.GammaS from hX).smul_left (-t)
    simpa [spectralCompactFlow] using hCommScaled.exp_left
  calc
    (T.spectralCompactFlow X t * Y * T.spectralCompactFlow X (-t)) * T.GammaS
        = T.spectralCompactFlow X t * Y * (T.spectralCompactFlow X (-t) * T.GammaS) := by
            simp [mul_assoc]
    _ = T.spectralCompactFlow X t * Y * (T.GammaS * T.spectralCompactFlow X (-t)) := by
          rw [hExpNeg.eq]
    _ = T.spectralCompactFlow X t * (Y * T.GammaS) * T.spectralCompactFlow X (-t) := by
          simp [mul_assoc]
    _ = T.spectralCompactFlow X t * (T.GammaS * Y) * T.spectralCompactFlow X (-t) := by
          rw [hY]
    _ = (T.spectralCompactFlow X t * T.GammaS) * Y * T.spectralCompactFlow X (-t) := by
          simp [mul_assoc]
    _ = (T.GammaS * T.spectralCompactFlow X t) * Y * T.spectralCompactFlow X (-t) := by
          rw [hExp.eq]
    _ = T.GammaS * (T.spectralCompactFlow X t * Y * T.spectralCompactFlow X (-t)) := by
          simp [mul_assoc]

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/--
Adjoint transport by a spectral compact flow preserves the noncompact sector.
-/
theorem spectralAdjointFlow_mem_noncompact
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {X Y : S}
    (hX : T.IsSpectralCompact X)
    (hY : T.IsSpectralNonCompact Y)
    (t : ℝ) :
    T.IsSpectralNonCompact (T.spectralAdjointFlow X t Y) := by
  rw [T.isSpectralCompact_iff_commute hD] at hX
  rw [T.isSpectralNonCompact_iff_anticommute hD] at hY ⊢
  unfold spectralAdjointFlow
  let e := T.spectralCompactFlow X t
  let f := T.spectralCompactFlow X (-t)
  have hExp : Commute e T.GammaS := by
    have hCommScaled : Commute (t • X) T.GammaS := by
      exact (show Commute X T.GammaS from hX).smul_left t
    simpa [e, spectralCompactFlow] using hCommScaled.exp_left
  have hExpNeg : Commute f T.GammaS := by
    have hCommScaled : Commute ((-t) • X) T.GammaS := by
      exact (show Commute X T.GammaS from hX).smul_left (-t)
    simpa [f, spectralCompactFlow] using hCommScaled.exp_left
  calc
    (e * Y * f) * T.GammaS = e * (Y * (f * T.GammaS)) := by
      simp [mul_assoc]
    _ = e * (Y * (T.GammaS * f)) := by
          rw [hExpNeg.eq]
    _ = (e * (Y * T.GammaS)) * f := by
          simp [mul_assoc]
    _ = (e * (-(T.GammaS * Y))) * f := by
          rw [hY]
    _ = (e * (-(T.GammaS * Y))) * f := by rfl
    _ = ((e * (-(T.GammaS * Y))) * f) := by rfl
    _ = -(e * ((T.GammaS * Y) * f)) := by
          calc
            (e * (-(T.GammaS * Y))) * f = (e * (-(T.GammaS * Y))) * f := rfl
            _ = (-(e * (T.GammaS * Y))) * f := by rw [mul_neg]
            _ = -(e * ((T.GammaS * Y) * f)) := by
                  simp [mul_assoc, neg_mul]
    _ = -((e * T.GammaS) * Y * f) := by
          simp [mul_assoc]
    _ = -((T.GammaS * e) * Y * f) := by
          rw [hExp.eq]
    _ = -(T.GammaS * (e * Y * f)) := by
          simp [mul_assoc]
    _ = -(T.GammaS * (T.spectralCompactFlow X t * Y * T.spectralCompactFlow X (-t))) := by
          simp [e, f]

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/--
Spectral-noncompact operators intertwine the grading flow with sign-reversed
time on the right.
-/
theorem mul_spectralGradingFlow_eq_spectralGradingFlow_neg_mul_of_anticommute_GammaS
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {Y : S}
    (hY : Y * T.GammaS = -(T.GammaS * Y))
    (t : ℝ) :
    Y * T.spectralGradingFlow t = T.spectralGradingFlow (-t) * Y := by
  rw [T.spectralGradingFlow_eq_cosh_add_sinh_GammaS hD t]
  rw [T.spectralGradingFlow_eq_cosh_add_sinh_GammaS hD (-t)]
  calc
    Y * (Real.cosh t • (1 : S) + Real.sinh t • T.GammaS)
        = Real.cosh t • Y - Real.sinh t • (T.GammaS * Y) := by
            rw [mul_add, mul_smul_comm, mul_smul_comm]
            simp [hY, sub_eq_add_neg]
    _ = Real.cosh (-t) • Y + Real.sinh (-t) • (T.GammaS * Y) := by
          simp [Real.cosh_neg, Real.sinh_neg, sub_eq_add_neg]
    _ = (Real.cosh (-t) • (1 : S) + Real.sinh (-t) • T.GammaS) * Y := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc]
          simp

omit [NormedAlgebra ℚ S] [CompleteSpace S] in
/--
Spectral-noncompact operators intertwine the grading flow with sign-reversed
time on the left.
-/
theorem spectralGradingFlow_mul_eq_mul_spectralGradingFlow_neg_of_anticommute_GammaS
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {Y : S}
    (hY : Y * T.GammaS = -(T.GammaS * Y))
    (t : ℝ) :
    T.spectralGradingFlow t * Y = Y * T.spectralGradingFlow (-t) := by
  have hY' : T.GammaS * Y = -(Y * T.GammaS) := by
    calc
      T.GammaS * Y = -(-(T.GammaS * Y)) := by simp
      _ = -(Y * T.GammaS) := by rw [hY]
  rw [T.spectralGradingFlow_eq_cosh_add_sinh_GammaS hD t]
  rw [T.spectralGradingFlow_eq_cosh_add_sinh_GammaS hD (-t)]
  calc
    (Real.cosh t • (1 : S) + Real.sinh t • T.GammaS) * Y
        = Real.cosh t • Y - Real.sinh t • (Y * T.GammaS) := by
            rw [add_mul, smul_mul_assoc, smul_mul_assoc]
            simp [hY', sub_eq_add_neg]
    _ = Real.cosh (-t) • Y + Real.sinh (-t) • (Y * T.GammaS) := by
          simp [Real.cosh_neg, Real.sinh_neg, sub_eq_add_neg]
    _ = Y * (Real.cosh (-t) • (1 : S) + Real.sinh (-t) • T.GammaS) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm]
          simp

/--
Under the spectral grading adjoint action, every spectral-noncompact operator is
transported explicitly by the doubled negative-time grading flow.
-/
theorem spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two_of_anticommute_GammaS
    {k : ℕ}
    (hD : IsDrazinInverse T.A T.A_D k)
    {Y : S}
    (hY : Y * T.GammaS = -(T.GammaS * Y))
    (t : ℝ) :
    T.spectralAdjointFlow T.GammaS t Y = Y * T.spectralGradingFlow (-(2 * t)) := by
  change T.spectralGradingFlow t * Y * T.spectralGradingFlow (-t) =
    Y * T.spectralGradingFlow (-(2 * t))
  rw [T.spectralGradingFlow_mul_eq_mul_spectralGradingFlow_neg_of_anticommute_GammaS hD hY t]
  rw [mul_assoc]
  rw [(T.spectralGradingFlow_add (-t) (-t)).symm]
  congr 1
  ring_nf

end Exponential

end InformationCartanTriple

end InfoGeometry.Canonical.CartanDecomposition
