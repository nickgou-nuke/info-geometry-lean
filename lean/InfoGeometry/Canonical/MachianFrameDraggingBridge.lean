/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import InfoGeometry.Physics.CrankingParity
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Machian Principles, Souriau Centrifuge, Frame-Dragging, & ZAMO Triplet Gap Restoration

Formalizes Machian inertial coupling and frame-dragging across three tiers, reusing
`DoubledMinkowskiRotatingSpinInstability` (`spinExchange4`, `totalSpinZ4`, `tripletProj4`,
`rotatingSpinHamiltonian`, `tripletPlusState`) and `CrankingParity` (`routhian`):

1. **Souriau Centrifuge & Machian Completion of the Square (Barbaresco Slide 83)**:
   Completes `E_co(p, r; Ω) = ‖p‖² / (2m) - Ω · (r × p)` into
   `‖p - m (Ω × r)‖² / (2m) - (m / 2) ‖Ω × r‖²`, proving unique global minimization at the
   rigidly co-rotating dragged momentum `p_* = m (Ω × r)`.
2. **Thirring–Lense Shell Frame-Dragging & Pure Machian Limit (`K_abs = 0`)**:
   Proves the variational inertial frequency `ω_* = (K_drag / (K_abs + K_drag)) Ω_shell` and
   exact locking `ω_* = Ω_shell` when absolute-space stiffness vanishes (`K_abs = 0`).
3. **ZAMO Triplet Zeeman Splitting Cancellation**:
   Embeds frame-dragging `Ω_drag` into `frameDraggedSpinHamiltonian J ω Ω_drag`, showing
   Triplet Zeeman splitting `E_{T,-1} - E_{T,+1} = 2 (ω - Ω_drag)` vanishes iff `ω = Ω_drag`
   (the locally non-rotating ZAMO observer), restoring the rest-frame Singlet–Triplet gap `J`,
   and connecting directly to `CrankingParity.routhian`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `zamo_triplet_zeeman_splitting_cancellation`
* `frameDraggedSpinHamiltonian_eq_cranking_routhian`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `souriau_centrifuge_machian_completion_of_square` (`0 < m`)
* `thirring_lense_shell_dragging_and_pure_mach_limit` (`0 ≤ K_abs`, `0 < K_drag`)

#### BUCKET 3: OPEN CLOSURE DEBT
* Derivation of `K_drag` and `Ω_drag` from global metric perturbations of linearized/nonlinear
  4D Einstein–Cartan cosmology remains outside this finite variational algebraic bridge.
-/

noncomputable section

open scoped Kronecker
open Matrix

namespace InfoGeometry.Canonical.MachianFrameDraggingBridge

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Physics.CrankingParity

/-! ### Part 1: Souriau Centrifuge & Machian Relative-Momentum Completion of the Square (Slide 83) -/

abbrev Vec3 := ℝ × ℝ × ℝ

def dot3 (u v : Vec3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def cross3 (u v : Vec3) : Vec3 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

def normSq3 (u : Vec3) : ℝ := dot3 u u

def sub3 (u v : Vec3) : Vec3 :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

def smul3 (c : ℝ) (u : Vec3) : Vec3 :=
  (c * u.1, c * u.2.1, c * u.2.2)

/-- Souriau co-moving energy `E_co(p, r; Ω) = ‖p‖² / (2m) - Ω · (r × p)` in a rotating frame `Ω`. -/
def souriauComovingEnergy (m : ℝ) (Ω r p : Vec3) : ℝ :=
  normSq3 p / (2 * m) - dot3 Ω (cross3 r p)

/-- Local frame-dragged equilibrium momentum `p_*(r) = m (Ω × r)`. -/
def draggedMomentum (m : ℝ) (Ω r : Vec3) : Vec3 :=
  smul3 m (cross3 Ω r)

/-- **Theorem 1 (Souriau Centrifuge Completion of the Square & Machian Co-Rotating Equilibrium)**:
For `m > 0`, `Ω · (r × p) = p · (Ω × r)`, `E_co(p, r; Ω)` completes into
`‖p - m(Ω × r)‖² / (2m) - (m/2) ‖Ω × r‖²`, and attains its unique global minimum at `p = m(Ω × r)`. -/
theorem souriau_centrifuge_machian_completion_of_square
    (m : ℝ) (hm : 0 < m) (Ω r p : Vec3) :
    let p_star := draggedMomentum m Ω r
    (dot3 Ω (cross3 r p) = dot3 p (cross3 Ω r)) ∧
    (souriauComovingEnergy m Ω r p =
      normSq3 (sub3 p p_star) / (2 * m) - (m / 2) * normSq3 (cross3 Ω r)) ∧
    (souriauComovingEnergy m Ω r p_star = -(m / 2) * normSq3 (cross3 Ω r)) ∧
    (souriauComovingEnergy m Ω r p_star ≤ souriauComovingEnergy m Ω r p) ∧
    (souriauComovingEnergy m Ω r p = souriauComovingEnergy m Ω r p_star ↔ p = p_star) := by
  dsimp
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have h2m_pos : 0 < 2 * m := by linarith [hm]
  have hTriple : dot3 Ω (cross3 r p) = dot3 p (cross3 Ω r) := by
    simp [dot3, cross3]; ring
  have hSquare : souriauComovingEnergy m Ω r p =
      normSq3 (sub3 p (draggedMomentum m Ω r)) / (2 * m) - (m / 2) * normSq3 (cross3 Ω r) := by
    unfold souriauComovingEnergy draggedMomentum normSq3 sub3 smul3 dot3 cross3
    field_simp [hm_ne]
    ring
  have hStarVal : souriauComovingEnergy m Ω r (draggedMomentum m Ω r) =
      -(m / 2) * normSq3 (cross3 Ω r) := by
    unfold souriauComovingEnergy draggedMomentum normSq3 smul3 dot3 cross3
    field_simp [hm_ne]
    ring
  have hNormNN : ∀ u : Vec3, 0 ≤ normSq3 u := fun u => by
    unfold normSq3 dot3
    exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
  have hNormZeroIff : ∀ u v : Vec3, normSq3 (sub3 u v) = 0 ↔ u = v := by
    intro u v
    unfold normSq3 sub3 dot3
    constructor
    · intro h0
      have h1 : (u.1 - v.1) ^ 2 = 0 := by
        nlinarith [h0, sq_nonneg (u.1 - v.1), sq_nonneg (u.2.1 - v.2.1), sq_nonneg (u.2.2 - v.2.2)]
      have h2 : (u.2.1 - v.2.1) ^ 2 = 0 := by
        nlinarith [h0, sq_nonneg (u.1 - v.1), sq_nonneg (u.2.1 - v.2.1), sq_nonneg (u.2.2 - v.2.2)]
      have h3 : (u.2.2 - v.2.2) ^ 2 = 0 := by
        nlinarith [h0, sq_nonneg (u.1 - v.1), sq_nonneg (u.2.1 - v.2.1), sq_nonneg (u.2.2 - v.2.2)]
      ext
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h3)
    · rintro rfl; ring
  refine ⟨hTriple, hSquare, hStarVal, ?_, ?_⟩
  · rw [hSquare, hStarVal]
    have hDivNN : 0 ≤ normSq3 (sub3 p (draggedMomentum m Ω r)) / (2 * m) :=
      div_nonneg (hNormNN _) h2m_pos.le
    linarith [hDivNN]
  · rw [hSquare, hStarVal, ← sub_eq_zero]
    have hSub : normSq3 (sub3 p (draggedMomentum m Ω r)) / (2 * m) -
        m / 2 * normSq3 (cross3 Ω r) - -(m / 2) * normSq3 (cross3 Ω r) =
        normSq3 (sub3 p (draggedMomentum m Ω r)) / (2 * m) := by ring
    rw [hSub, div_eq_zero_iff, or_iff_left (ne_of_gt h2m_pos)]
    exact hNormZeroIff p (draggedMomentum m Ω r)

/-! ### Part 2: Thirring–Lense Shell Frame-Dragging & The Pure Machian Limit (`K_abs = 0`) -/

/-- Variational frame-dragging energy `E_Mach(ω) = ½ K_abs ω² + ½ K_drag (ω - Ω_shell)²`. -/
def machShellEnergy (K_abs K_drag Ω_shell ω : ℝ) : ℝ :=
  (1 / 2 : ℝ) * K_abs * ω ^ 2 + (1 / 2 : ℝ) * K_drag * (ω - Ω_shell) ^ 2

/-- Dragged inertial angular velocity `ω_* = (K_drag / (K_abs + K_drag)) * Ω_shell`. -/
def draggedInertialFreq (K_abs K_drag Ω_shell : ℝ) : ℝ :=
  (K_drag / (K_abs + K_drag)) * Ω_shell

/-- **Theorem 2 (Thirring–Lense Frame-Dragging Ratio & Pure Machian Locking `K_abs = 0 ⟹ ω_* = Ω_shell`)**:
For `0 ≤ K_abs` and `0 < K_drag`, `E_Mach(ω)` is minimized uniquely at `ω_*`, and vanishes into
full frame-dragging `ω_* = Ω_shell` when `K_abs = 0`. -/
theorem thirring_lense_shell_dragging_and_pure_mach_limit
    (K_abs K_drag Ω_shell ω : ℝ)
    (hAbs : 0 ≤ K_abs) (hDrag : 0 < K_drag) :
    let ω_star := draggedInertialFreq K_abs K_drag Ω_shell
    (machShellEnergy K_abs K_drag Ω_shell ω -
      machShellEnergy K_abs K_drag Ω_shell ω_star =
      ((K_abs + K_drag) / 2) * (ω - ω_star) ^ 2) ∧
    (machShellEnergy K_abs K_drag Ω_shell ω_star ≤
      machShellEnergy K_abs K_drag Ω_shell ω) ∧
    (K_abs = 0 → ω_star = Ω_shell) := by
  dsimp
  have hSumPos : 0 < K_abs + K_drag := by linarith [hAbs, hDrag]
  have hSumNe : K_abs + K_drag ≠ 0 := ne_of_gt hSumPos
  have hDiff : machShellEnergy K_abs K_drag Ω_shell ω -
      machShellEnergy K_abs K_drag Ω_shell (draggedInertialFreq K_abs K_drag Ω_shell) =
      ((K_abs + K_drag) / 2) * (ω - draggedInertialFreq K_abs K_drag Ω_shell) ^ 2 := by
    unfold machShellEnergy draggedInertialFreq
    field_simp [hSumNe]
    ring
  refine ⟨hDiff, ?_, ?_⟩
  · have hNN : 0 ≤ ((K_abs + K_drag) / 2) *
        (ω - draggedInertialFreq K_abs K_drag Ω_shell) ^ 2 :=
      mul_nonneg (by linarith [hSumPos]) (sq_nonneg _)
    linarith [hDiff, hNN]
  · intro hAbs0
    unfold draggedInertialFreq
    rw [hAbs0, zero_add, div_self (ne_of_gt hDrag), one_mul]

/-! ### Part 3: ZAMO (Zero Angular Momentum Observer) & Triplet Zeeman Splitting Cancellation -/

/-- Frame-dragged two-spin Hamiltonian `H_ZAMO(J, ω, Ω_drag) = rotatingSpinHamiltonian J (ω - Ω_drag)`,
reusing `DoubledMinkowskiRotatingSpinInstability.rotatingSpinHamiltonian`. -/
def frameDraggedSpinHamiltonian (J ω Ω_drag : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  rotatingSpinHamiltonian J (ω - Ω_drag)

/-- Counter-rotating `m = -1` Triplet state `ψ_{T,-1} = e₁ ⊗ e₁`. -/
def tripletMinusState : Fin 2 × Fin 2 → ℝ
  | (0, 0) => 0
  | (0, 1) => 0
  | (1, 0) => 0
  | (1, 1) => 1

private lemma zamo_zeeman_gap_iff (J ω Ω_drag : ℝ) :
    ((1 / 4 : ℝ) * J + (ω - Ω_drag)) - ((1 / 4 : ℝ) * J - (ω - Ω_drag)) = 2 * (ω - Ω_drag) ∧
    (((1 / 4 : ℝ) * J + (ω - Ω_drag) = (1 / 4 : ℝ) * J - (ω - Ω_drag)) ↔ ω = Ω_drag) ∧
    (ω = Ω_drag →
      ((1 / 4 : ℝ) * J - (ω - Ω_drag)) - -(3 / 4 : ℝ) * J = J ∧
      ((1 / 4 : ℝ) * J + (ω - Ω_drag)) - -(3 / 4 : ℝ) * J = J) := by
  refine ⟨by ring, ⟨fun h => by linarith [h], fun h => by subst h; ring⟩,
    fun h => by subst h; constructor <;> ring⟩

private lemma zamo_triplet_minus_scalar (J ω Ω_drag : ℝ) :
    (J / 4 : ℝ) - (ω - Ω_drag) * (-1 : ℝ) = (1 / 4 : ℝ) * J + (ω - Ω_drag) := by
  ring

/-- **Theorem 3 (ZAMO Frame-Dragging Condition & Triplet Zeeman Splitting Cancellation)**:
Reusing `DoubledMinkowskiRotatingSpinInstability`:
1. `m = +1` Triplet energy is `E_{T,+1} = J / 4 - (ω - Ω_drag)` and `m = -1` Triplet energy
   is `E_{T,-1} = J / 4 + (ω - Ω_drag)`.
2. Triplet Zeeman splitting `E_{T,-1} - E_{T,+1} = 2 (ω - Ω_drag)` vanishes iff `ω = Ω_drag`
   (the locally non-rotating ZAMO observer), restoring the rest-frame Singlet–Triplet gap `J`. -/
theorem zamo_triplet_zeeman_splitting_cancellation (J ω Ω_drag : ℝ) :
    let H := frameDraggedSpinHamiltonian J ω Ω_drag
    let E_plus := (1 / 4 : ℝ) * J - (ω - Ω_drag)
    let E_minus := (1 / 4 : ℝ) * J + (ω - Ω_drag)
    (H.mulVec tripletPlusState = E_plus • tripletPlusState) ∧
    (H.mulVec tripletMinusState = E_minus • tripletMinusState) ∧
    (E_minus - E_plus = 2 * (ω - Ω_drag)) ∧
    (E_minus = E_plus ↔ ω = Ω_drag) ∧
    (ω = Ω_drag →
      E_plus - -(3 / 4 : ℝ) * J = J ∧ E_minus - -(3 / 4 : ℝ) * J = J) := by
  dsimp
  have hGap := zamo_zeeman_gap_iff J ω Ω_drag
  have hPlus : (frameDraggedSpinHamiltonian J ω Ω_drag).mulVec tripletPlusState =
      ((1 / 4 : ℝ) * J - (ω - Ω_drag)) • tripletPlusState :=
    (real_rotating_frame_singlet_triplet_instability J (ω - Ω_drag)).2.2.2.2.1
  have hPT_minus : tripletProj4.mulVec tripletMinusState = tripletMinusState := by
    ext ⟨i₁, i₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      (simp [tripletProj4, swapOp4, spinExchange4, tripletMinusState, zCut2, xMir2, eps2,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; try norm_num)
  have hEx_minus : spinExchange4.mulVec tripletMinusState = tripletMinusState := by
    calc
      spinExchange4.mulVec tripletMinusState =
          spinExchange4.mulVec (tripletProj4.mulVec tripletMinusState) := by rw [hPT_minus]
      _ = (spinExchange4 * tripletProj4).mulVec tripletMinusState := Matrix.mulVec_mulVec _ _ _
      _ = tripletProj4.mulVec tripletMinusState := by
        rw [real_singlet_triplet_decomposition_and_casimir_splitting.2.2.1.2]
      _ = tripletMinusState := hPT_minus
  have hZ_minus : totalSpinZ4.mulVec tripletMinusState = (-1 : ℝ) • tripletMinusState := by
    ext ⟨i₁, i₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      (simp [totalSpinZ4, tripletMinusState, zCut2, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two]; try norm_num)
  refine ⟨hPlus, ?_, hGap.1, hGap.2.1, hGap.2.2⟩
  unfold frameDraggedSpinHamiltonian rotatingSpinHamiltonian
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hEx_minus, hZ_minus,
    smul_smul, ← sub_smul, zamo_triplet_minus_scalar]

/-- CrankingParity bridge: `Matrix.toLin' (frameDraggedSpinHamiltonian J ω Ω_drag)` is the
Inglis cranking Routhian shifted to relative angular velocity `ω - Ω_drag`. -/
theorem frameDraggedSpinHamiltonian_eq_cranking_routhian (J ω Ω_drag : ℝ) :
    Matrix.toLin' (frameDraggedSpinHamiltonian J ω Ω_drag) =
      routhian (Matrix.toLin' ((J / 4 : ℝ) • spinExchange4))
        (Matrix.toLin' totalSpinZ4) (ω - Ω_drag) := by
  unfold frameDraggedSpinHamiltonian rotatingSpinHamiltonian routhian
  rw [map_sub, map_smul, map_smul]

end InfoGeometry.Canonical.MachianFrameDraggingBridge
