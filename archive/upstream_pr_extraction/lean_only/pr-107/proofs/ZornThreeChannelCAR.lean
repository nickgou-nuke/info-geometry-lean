import proofs.ZornLightconeChannelOperator
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Full three-channel Zorn CAR

This module determines all anticommutators of the six directed lightcone
operators.  The resulting algebra is color-resolved: the mixed
anticommutator is an operator `C r s`, not a scalar Kronecker delta.
-/

noncomputable section

namespace ZornThreeChannelCAR

open InfoGeometry.Physics.SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornChiralLightcone ZornLightconeCAR

/-- The color-resolved mixed anticommutator. -/
def threeChannelMixed (r s : Fin 3) : Module.End ℂ DiracSpinor16 :=
  lightconeSigmaPlus r * lightconeSigmaMinus s +
    lightconeSigmaMinus s * lightconeSigmaPlus r

/-- Complex-valued Kronecker delta on the three color channels. -/
def colorDelta (r s : Fin 3) : ℂ := if r = s then 1 else 0

@[simp] theorem colorDelta_self (r : Fin 3) : colorDelta r r = 1 := by
  simp [colorDelta]

theorem colorDelta_of_ne {r s : Fin 3} (h : r ≠ s) :
    colorDelta r s = 0 := by
  simp [colorDelta, h]

/-- Exact positive-semispinor block of the mixed channel operator. -/
def mixedPlusZorn (r s : Fin 3) (X : Zorn) : Zorn where
  a := -colorDelta r s * X.a
  u := fun i => -colorDelta i r * X.u s
  v := fun i => colorDelta i s * X.v r - colorDelta r s * X.v i
  b := 0

/-- Exact negative-semispinor block of the mixed channel operator. -/
def mixedMinusZorn (r s : Fin 3) (X : Zorn) : Zorn where
  a := 0
  u := fun i => colorDelta i r * X.u s - colorDelta r s * X.u i
  v := fun i => -colorDelta i s * X.v r
  b := -colorDelta r s * X.b

/-! The off-diagonal terms are color matrix units, not zero. -/

theorem mixedPlusZorn_offdiag {r s : Fin 3} (h : r ≠ s) (X : Zorn) :
    mixedPlusZorn r s X =
      { a := 0
        u := fun i => if i = r then -X.u s else 0
        v := fun i => if i = s then X.v r else 0
        b := 0 } := by
  apply zorn_ext
  · simp [mixedPlusZorn, colorDelta_of_ne h]
  · funext i
    by_cases hir : i = r <;>
      simp [mixedPlusZorn, colorDelta, hir]
  · funext i
    by_cases his : i = s <;>
      simp [mixedPlusZorn, colorDelta, h, his]
  · rfl

theorem mixedMinusZorn_offdiag {r s : Fin 3} (h : r ≠ s) (X : Zorn) :
    mixedMinusZorn r s X =
      { a := 0
        u := fun i => if i = r then X.u s else 0
        v := fun i => if i = s then -X.v r else 0
        b := 0 } := by
  apply zorn_ext
  · rfl
  · funext i
    by_cases hir : i = r <;>
      simp [mixedMinusZorn, colorDelta, h, hir]
  · funext i
    by_cases his : i = s <;>
      simp [mixedMinusZorn, colorDelta, his]
  · simp [mixedMinusZorn, colorDelta_of_ne h]

/-- On the diagonal, the positive block reduces to the classified channel block. -/
theorem mixedPlusZorn_diag (r : Fin 3) (X : Zorn) :
    mixedPlusZorn r r X =
      ZornLightconeChannelOperator.channelPlusZorn r X := by
  apply zorn_ext
  · simp [mixedPlusZorn,
      ZornLightconeChannelOperator.channelPlusZorn]
  · funext i
    by_cases h : i = r
    · subst i
      simp [mixedPlusZorn,
        ZornLightconeChannelOperator.channelPlusZorn, colorDelta]
    · simp [mixedPlusZorn,
        ZornLightconeChannelOperator.channelPlusZorn, colorDelta, h]
  · funext i
    by_cases h : i = r <;>
      simp [mixedPlusZorn,
        ZornLightconeChannelOperator.channelPlusZorn, colorDelta, h]
  · rfl

/-- On the diagonal, the negative block reduces to the classified channel block. -/
theorem mixedMinusZorn_diag (r : Fin 3) (X : Zorn) :
    mixedMinusZorn r r X =
      ZornLightconeChannelOperator.channelMinusZorn r X := by
  apply zorn_ext
  · rfl
  · funext i
    by_cases h : i = r <;>
      simp [mixedMinusZorn,
        ZornLightconeChannelOperator.channelMinusZorn, colorDelta, h]
  · funext i
    by_cases h : i = r
    · subst i
      simp [mixedMinusZorn,
        ZornLightconeChannelOperator.channelMinusZorn, colorDelta]
    · simp [mixedMinusZorn,
        ZornLightconeChannelOperator.channelMinusZorn, colorDelta, h]
  · simp [mixedMinusZorn,
      ZornLightconeChannelOperator.channelMinusZorn, colorDelta]

/-- Two positive directed operators compose to zero, in every pair of channels. -/
theorem lightconeSigmaPlus_mul_plus (r s : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaPlus s = 0 := by
  rw [lightconeSigmaPlus]
  calc
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) *
        (peirceProjectorMinus * peirceProjectorPlus) *
        diracGamma (upperLightconeVector s) * peirceProjectorMinus := by
      noncomm_ring
    _ = 0 := by rw [peirceProjectorMinus_mul_plus]; simp

/-- Two negative directed operators compose to zero, in every pair of channels. -/
theorem lightconeSigmaMinus_mul_minus (r s : Fin 3) :
    lightconeSigmaMinus r * lightconeSigmaMinus s = 0 := by
  rw [lightconeSigmaMinus]
  calc
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) *
        (peirceProjectorPlus * peirceProjectorMinus) *
        diracGamma (lowerLightconeVector s) * peirceProjectorPlus := by
      noncomm_ring
    _ = 0 := by rw [peirceProjectorPlus_mul_minus]; simp

/-- The first mixed Zorn composition, fully reduced to color coordinates. -/
theorem clifford_mixed_plus_exact (r s : Fin 3) (S : SpinorPlus8) :
    (cliffordMinus (upperLightconeVector r)
      (cliffordPlus (lowerLightconeVector s) S)).val =
        mixedPlusZorn r s S.val := by
  fin_cases r <;> fin_cases s <;> apply zorn_ext
  all_goals
    simp [cliffordMinus, cliffordPlus, upperLightconeVector,
      lowerLightconeVector, zornConj, zornMul, mixedPlusZorn,
      colorDelta, E_k, F_k, e_k, dot3, cross3]
  all_goals
    funext i
    fin_cases i <;> simp

/-- The second mixed Zorn composition, fully reduced to color coordinates. -/
theorem clifford_mixed_minus_exact (r s : Fin 3) (C : SpinorMinus8) :
    (cliffordPlus (lowerLightconeVector s)
      (cliffordMinus (upperLightconeVector r) C)).val =
        mixedMinusZorn r s C.val := by
  fin_cases r <;> fin_cases s <;> apply zorn_ext
  all_goals
    simp [cliffordMinus, cliffordPlus, upperLightconeVector,
      lowerLightconeVector, zornConj, zornMul, mixedMinusZorn,
      colorDelta, E_k, F_k, e_k, dot3, cross3]
  all_goals
    funext i
    fin_cases i <;> simp

/-- The full positive-positive anticommutator vanishes. -/
theorem lightconeSigmaPlus_anticommutator (r s : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaPlus s +
      lightconeSigmaPlus s * lightconeSigmaPlus r = 0 := by
  rw [lightconeSigmaPlus_mul_plus, lightconeSigmaPlus_mul_plus]
  exact add_zero 0

/-- The full negative-negative anticommutator vanishes. -/
theorem lightconeSigmaMinus_anticommutator (r s : Fin 3) :
    lightconeSigmaMinus r * lightconeSigmaMinus s +
      lightconeSigmaMinus s * lightconeSigmaMinus r = 0 := by
  rw [lightconeSigmaMinus_mul_minus, lightconeSigmaMinus_mul_minus]
  exact add_zero 0

/-- Exact positive-after-negative action for arbitrary channel indices. -/
@[simp] theorem lightconeSigmaPlus_mul_minus_apply (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaPlus r (lightconeSigmaMinus s (S, C)) =
      (cliffordMinus (upperLightconeVector r)
        (cliffordPlus (lowerLightconeVector s) S), 0) := by
  rw [lightconeSigmaMinus_apply, lightconeSigmaPlus_apply]

/-- Exact negative-after-positive action for arbitrary channel indices. -/
@[simp] theorem lightconeSigmaMinus_mul_plus_apply (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaMinus s (lightconeSigmaPlus r (S, C)) =
      (0, cliffordPlus (lowerLightconeVector s)
        (cliffordMinus (upperLightconeVector r) C)) := by
  rw [lightconeSigmaPlus_apply, lightconeSigmaMinus_apply]

/-- The mixed CAR relation for arbitrary channel indices. -/
theorem lightconeSigma_mixed_anticommutator (r s : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaMinus s +
      lightconeSigmaMinus s * lightconeSigmaPlus r =
        threeChannelMixed r s := by
  rfl

/-- The diagonal of the three-channel matrix is the previously classified channel operator. -/
theorem threeChannelMixed_diag (r : Fin 3) :
    threeChannelMixed r r = lightconeChannelProjector r := by
  rfl

/-- A positive-semispinor witness selecting the upper color coordinate `s`. -/
def upperChannelSpinor (s : Fin 3) : SpinorPlus8 := ⟨E_k s⟩

private theorem mixedWitnessCoordinate_r0 (s : Fin 3) :
    (cliffordMinus (upperLightconeVector 0)
      (cliffordPlus (lowerLightconeVector s) (upperChannelSpinor s))).val.u 0 = -1 := by
  fin_cases s <;>
    simp [upperChannelSpinor, cliffordMinus, cliffordPlus,
      upperLightconeVector, lowerLightconeVector, zornConj, zornMul,
      E_k, F_k, e_k, dot3, cross3]

private theorem mixedWitnessCoordinate_r1 (s : Fin 3) :
    (cliffordMinus (upperLightconeVector 1)
      (cliffordPlus (lowerLightconeVector s) (upperChannelSpinor s))).val.u 1 = -1 := by
  fin_cases s <;>
    simp [upperChannelSpinor, cliffordMinus, cliffordPlus,
      upperLightconeVector, lowerLightconeVector, zornConj, zornMul,
      E_k, F_k, e_k, dot3, cross3]

private theorem mixedWitnessCoordinate_r2 (s : Fin 3) :
    (cliffordMinus (upperLightconeVector 2)
      (cliffordPlus (lowerLightconeVector s) (upperChannelSpinor s))).val.u 2 = -1 := by
  fin_cases s <;>
    simp [upperChannelSpinor, cliffordMinus, cliffordPlus,
      upperLightconeVector, lowerLightconeVector, zornConj, zornMul,
      E_k, F_k, e_k, dot3, cross3]

/-- The mixed action has a uniformly nonzero `u r` witness for every pair. -/
theorem mixedWitnessCoordinate (r s : Fin 3) :
    (cliffordMinus (upperLightconeVector r)
      (cliffordPlus (lowerLightconeVector s) (upperChannelSpinor s))).val.u r = -1 := by
  fin_cases r
  · exact mixedWitnessCoordinate_r0 s
  · exact mixedWitnessCoordinate_r1 s
  · exact mixedWitnessCoordinate_r2 s

/-- The positive-after-negative summand is nonzero in all nine channel pairs. -/
theorem lightconeSigmaPlus_mul_minus_ne_zero (r s : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaMinus s ≠ 0 := by
  intro hzero
  have happ := LinearMap.congr_fun hzero (upperChannelSpinor s, 0)
  have hu := congrArg (fun X : DiracSpinor16 => X.1.val.u r) happ
  rw [Module.End.mul_apply,
    lightconeSigmaPlus_mul_minus_apply] at hu
  simp only [LinearMap.zero_apply] at hu
  rw [mixedWitnessCoordinate] at hu
  norm_num at hu

/-- The positive Peirce projection fixes every positive directed operator. -/
theorem peirceProjectorPlus_mul_sigmaPlus (r : Fin 3) :
    peirceProjectorPlus * lightconeSigmaPlus r = lightconeSigmaPlus r := by
  rw [lightconeSigmaPlus]
  calc
    _ = (peirceProjectorPlus * peirceProjectorPlus) *
        diracGamma (upperLightconeVector r) * peirceProjectorMinus := by
      noncomm_ring
    _ = _ := by rw [peirceProjectorPlus_sq]

/-- The positive Peirce projection kills every negative directed operator. -/
theorem peirceProjectorPlus_mul_sigmaMinus (r : Fin 3) :
    peirceProjectorPlus * lightconeSigmaMinus r = 0 := by
  rw [lightconeSigmaMinus]
  calc
    _ = (peirceProjectorPlus * peirceProjectorMinus) *
        diracGamma (lowerLightconeVector r) * peirceProjectorPlus := by
      noncomm_ring
    _ = 0 := by rw [peirceProjectorPlus_mul_minus]; simp

/-- The positive Peirce block of a mixed CAR entry is its first summand. -/
theorem peirceProjectorPlus_mul_threeChannelMixed (r s : Fin 3) :
    peirceProjectorPlus * threeChannelMixed r s =
      lightconeSigmaPlus r * lightconeSigmaMinus s := by
  rw [threeChannelMixed, mul_add,
    ← mul_assoc, peirceProjectorPlus_mul_sigmaPlus,
    ← mul_assoc, peirceProjectorPlus_mul_sigmaMinus]
  simp

/-- The negative Peirce projection kills every positive directed operator. -/
theorem peirceProjectorMinus_mul_sigmaPlus (r : Fin 3) :
    peirceProjectorMinus * lightconeSigmaPlus r = 0 := by
  rw [lightconeSigmaPlus]
  calc
    _ = (peirceProjectorMinus * peirceProjectorPlus) *
        diracGamma (upperLightconeVector r) * peirceProjectorMinus := by
      noncomm_ring
    _ = 0 := by rw [peirceProjectorMinus_mul_plus]; simp

/-- The negative Peirce projection fixes every negative directed operator. -/
theorem peirceProjectorMinus_mul_sigmaMinus (r : Fin 3) :
    peirceProjectorMinus * lightconeSigmaMinus r = lightconeSigmaMinus r := by
  rw [lightconeSigmaMinus]
  calc
    _ = (peirceProjectorMinus * peirceProjectorMinus) *
        diracGamma (lowerLightconeVector r) * peirceProjectorPlus := by
      noncomm_ring
    _ = _ := by rw [peirceProjectorMinus_sq]

/-- The negative Peirce block of a mixed CAR entry is its second summand. -/
theorem peirceProjectorMinus_mul_threeChannelMixed (r s : Fin 3) :
    peirceProjectorMinus * threeChannelMixed r s =
      lightconeSigmaMinus s * lightconeSigmaPlus r := by
  rw [threeChannelMixed, mul_add,
    ← mul_assoc, peirceProjectorMinus_mul_sigmaPlus,
    ← mul_assoc, peirceProjectorMinus_mul_sigmaMinus]
  simp

/-- Calculated positive chiral block of the mixed anticommutator. -/
theorem threeChannelMixed_fst_exact (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (threeChannelMixed r s (S, C)).1.val = mixedPlusZorn r s S.val := by
  have h := LinearMap.congr_fun
    (peirceProjectorPlus_mul_threeChannelMixed r s) (S, C)
  have hf := congrArg (fun X : DiracSpinor16 => X.1) h
  have hf' : (threeChannelMixed r s (S, C)).1 =
      cliffordMinus (upperLightconeVector r)
        (cliffordPlus (lowerLightconeVector s) S) := by
    generalize hY : threeChannelMixed r s (S, C) = Y at hf ⊢
    rcases Y with ⟨S', C'⟩
    rw [Module.End.mul_apply, hY, peirceProjectorPlus_apply] at hf
    rw [Module.End.mul_apply, lightconeSigmaPlus_mul_minus_apply] at hf
    exact hf
  exact (congrArg ZornCopy.val hf').trans (clifford_mixed_plus_exact r s S)

/-- Calculated negative chiral block of the mixed anticommutator. -/
theorem threeChannelMixed_snd_exact (r s : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (threeChannelMixed r s (S, C)).2.val = mixedMinusZorn r s C.val := by
  have h := LinearMap.congr_fun
    (peirceProjectorMinus_mul_threeChannelMixed r s) (S, C)
  have hs := congrArg (fun X : DiracSpinor16 => X.2) h
  have hs' : (threeChannelMixed r s (S, C)).2 =
      cliffordPlus (lowerLightconeVector s)
        (cliffordMinus (upperLightconeVector r) C) := by
    generalize hY : threeChannelMixed r s (S, C) = Y at hs ⊢
    rcases Y with ⟨S', C'⟩
    rw [Module.End.mul_apply, hY, peirceProjectorMinus_apply] at hs
    rw [Module.End.mul_apply, lightconeSigmaMinus_mul_plus_apply] at hs
    exact hs
  exact (congrArg ZornCopy.val hs').trans (clifford_mixed_minus_exact r s C)

/-- The mixed anticommutator is nonzero for every diagonal or off-diagonal pair. -/
theorem threeChannelMixed_ne_zero (r s : Fin 3) :
    threeChannelMixed r s ≠ 0 := by
  intro hzero
  have h := congrArg (fun A : Module.End ℂ DiracSpinor16 =>
    peirceProjectorPlus * A) hzero
  change peirceProjectorPlus * threeChannelMixed r s =
    peirceProjectorPlus * 0 at h
  rw [peirceProjectorPlus_mul_threeChannelMixed, mul_zero] at h
  exact lightconeSigmaPlus_mul_minus_ne_zero r s h

/-- The six directed generators of the three-channel system. -/
inductive LightconeMode where
  | plus (r : Fin 3)
  | minus (r : Fin 3)
  deriving DecidableEq

/-- Operator represented by a directed channel label. -/
def lightconeModeOperator : LightconeMode → Module.End ℂ DiracSpinor16
  | .plus r => lightconeSigmaPlus r
  | .minus r => lightconeSigmaMinus r

/-- The complete `6 × 6` operator-valued CAR matrix. -/
def lightconeCARMatrix (m n : LightconeMode) :
    Module.End ℂ DiracSpinor16 :=
  lightconeModeOperator m * lightconeModeOperator n +
    lightconeModeOperator n * lightconeModeOperator m

/-- Every entry of the full `6 × 6` CAR matrix, by channel and direction. -/
theorem lightconeCARMatrix_entries (m n : LightconeMode) :
    lightconeCARMatrix m n =
      match m, n with
      | .plus _, .plus _ => 0
      | .minus _, .minus _ => 0
      | .plus r, .minus s => threeChannelMixed r s
      | .minus r, .plus s => threeChannelMixed s r := by
  cases m with
  | plus r =>
      cases n with
      | plus s => exact lightconeSigmaPlus_anticommutator r s
      | minus s => rfl
  | minus r =>
      cases n with
      | plus s =>
          change lightconeSigmaMinus r * lightconeSigmaPlus s +
              lightconeSigmaPlus s * lightconeSigmaMinus r =
            lightconeSigmaPlus s * lightconeSigmaMinus r +
              lightconeSigmaMinus r * lightconeSigmaPlus s
          exact add_comm _ _
      | minus s => exact lightconeSigmaMinus_anticommutator r s

/-- Capstone form of the full three-channel CAR. -/
theorem full_three_channel_CAR :
    (∀ r s : Fin 3,
      lightconeSigmaPlus r * lightconeSigmaPlus s +
        lightconeSigmaPlus s * lightconeSigmaPlus r = 0) ∧
    (∀ r s : Fin 3,
      lightconeSigmaMinus r * lightconeSigmaMinus s +
        lightconeSigmaMinus s * lightconeSigmaMinus r = 0) ∧
    (∀ r s : Fin 3,
      lightconeSigmaPlus r * lightconeSigmaMinus s +
        lightconeSigmaMinus s * lightconeSigmaPlus r =
          threeChannelMixed r s) ∧
    (∀ (r s : Fin 3) (S : SpinorPlus8),
      (cliffordMinus (upperLightconeVector r)
        (cliffordPlus (lowerLightconeVector s) S)).val =
          mixedPlusZorn r s S.val) ∧
    (∀ (r s : Fin 3) (C : SpinorMinus8),
      (cliffordPlus (lowerLightconeVector s)
        (cliffordMinus (upperLightconeVector r) C)).val =
          mixedMinusZorn r s C.val) ∧
    (∀ r : Fin 3,
      threeChannelMixed r r = lightconeChannelProjector r) ∧
    (∀ r s : Fin 3, threeChannelMixed r s ≠ 0) := by
  exact ⟨lightconeSigmaPlus_anticommutator,
    lightconeSigmaMinus_anticommutator,
    lightconeSigma_mixed_anticommutator,
    clifford_mixed_plus_exact,
    clifford_mixed_minus_exact,
    threeChannelMixed_diag,
    threeChannelMixed_ne_zero⟩

end ZornThreeChannelCAR

end noncomputable section
