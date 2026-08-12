import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Meta.Architecture

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.CuntzKTowerCommutation

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Cuntz/K-linear commutation via the `Cl(1,1)` tower colimit

This file proves the algebraic direct-limit part of the Cuntz/phase-axis
commutation problem.

It does not construct the analytic Cuntz shift on an `ℓ²` completion. Instead
it proves the owner theorem that Path 2 can honestly close now: compatible
finite-stage representatives that commute at every stage have commuting images
in the `Cl(1,1)` tensor-tower direct limit.
-/

abbrev TowerStage (n : ℕ) : Type :=
  Stage n

abbrev TowerLimit : Type :=
  Limit

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

* `stageK_commutes_bond`
* `limitElement_eq_stage`
* `stageShift_preserves_compatibleK`
* `limitK_wellDefined`
* `compatible_limit_commute`
* `S_left_commutes_K_limit`
* `phaseAxisMatrix_sq`
* `stageKFromOne_commutes_bond`
* `limitKFromOne_wellDefined`
* `compatible_limit_commute_from_one`
* `S_left_commutes_K_limit_from_one`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

* `stageK_commutes_bond`
* `limitElement_eq_stage`
* `stageShift_preserves_compatibleK`
* `limitK_wellDefined`
* `compatible_limit_commute`
* `S_left_commutes_K_limit`
* `compatible_limit_commute_from_one`
* `S_left_commutes_K_limit_from_one`

#### BUCKET 3: OPEN CLOSURE DEBT
[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses,
certificates, or renamed placeholders.]

* Construct the concrete analytic `S_left` on the intended `ℓ²` Cantor-boundary
  completion.
* Construct the concrete finite-stage phase-axis representatives `Kstage n`.
* Prove the concrete compatibility laws
  `stageEmbed n (S_left n) = S_left (n + 1)` and
  `stageEmbed n (Kstage n) = Kstage (n + 1)`.
* Prove the finite-stage commutation law
  `S_left n * Kstage n = Kstage n * S_left n`.
-/

/-- The direct-limit element represented by stage zero of a compatible sequence. -/
@[rep_depth operator]
def limitElement (F : ∀ n : ℕ, TowerStage n) : TowerLimit :=
  ofStage 0 (F 0)

/-- Read back the stage-bond compatibility of a proposed phase-axis sequence. -/
@[rep_depth operator]
theorem stageK_commutes_bond
    (Kstage : ∀ n : ℕ, TowerStage n)
    (hK : ∀ n : ℕ, stageEmbed n (Kstage n) = Kstage (n + 1))
    (n : ℕ) :
    stageEmbed n (Kstage n) = Kstage (n + 1) :=
  hK n

/--
Any compatible finite-stage sequence has a stage-independent direct-limit image.
-/
@[rep_depth operator]
theorem limitElement_eq_stage
    (F : ∀ n : ℕ, TowerStage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1))
    (n : ℕ) :
    ofStage n (F n) = limitElement F :=
  finite_sequence_constant_in_limit F hF n

/--
The tower shift preserves a compatible phase-axis representative after canonical
insertion into the direct limit.
-/
@[rep_depth operator]
theorem stageShift_preserves_compatibleK
    (Kstage : ∀ n : ℕ, TowerStage n)
    (hK : ∀ n : ℕ, stageEmbed n (Kstage n) = Kstage (n + 1))
    (n : ℕ) :
    ofStage (n + 1) (Kstage (n + 1)) = ofStage n (Kstage n) := by
  rw [← hK n]
  exact ofStage_apply_bond n (Kstage n)

/-- The colimit phase-axis element represented by a compatible stage sequence. -/
@[rep_depth operator]
def limitK (Kstage : ∀ n : ℕ, TowerStage n) : TowerLimit :=
  limitElement Kstage

/-- The phase-axis representative is independent of the finite stage in the limit. -/
@[rep_depth operator]
theorem limitK_wellDefined
    (Kstage : ∀ n : ℕ, TowerStage n)
    (hK : ∀ n : ℕ, stageEmbed n (Kstage n) = Kstage (n + 1))
    (n : ℕ) :
    ofStage n (Kstage n) = limitK Kstage :=
  limitElement_eq_stage Kstage hK n

/--
Compatible finite-stage representatives that commute at every stage have
commuting images in the direct limit.
-/
@[rep_depth operator]
theorem compatible_limit_commute
    (A B : ∀ n : ℕ, TowerStage n)
    (hA : ∀ n : ℕ, stageEmbed n (A n) = A (n + 1))
    (hB : ∀ n : ℕ, stageEmbed n (B n) = B (n + 1))
    (hcomm : ∀ n : ℕ, A n * B n = B n * A n)
    (n : ℕ) :
    limitElement A * limitElement B = limitElement B * limitElement A := by
  calc
    limitElement A * limitElement B
        = ofStage n (A n) * ofStage n (B n) := by
            rw [limitElement_eq_stage A hA n, limitElement_eq_stage B hB n]
    _ = ofStage n (B n) * ofStage n (A n) := by
            exact limit_commute (n := n) (hcomm n)
    _ = limitElement B * limitElement A := by
            rw [limitElement_eq_stage B hB n, limitElement_eq_stage A hA n]

/--
Path-2 Cuntz/K commutation theorem.

If `S_left` and `Kstage` are compatible finite-stage representatives and commute
at each finite stage, their colimit images commute.
-/
@[rep_depth operator]
theorem S_left_commutes_K_limit
    (S_left Kstage : ∀ n : ℕ, TowerStage n)
    (hS : ∀ n : ℕ, stageEmbed n (S_left n) = S_left (n + 1))
    (hK : ∀ n : ℕ, stageEmbed n (Kstage n) = Kstage (n + 1))
    (hcomm : ∀ n : ℕ, S_left n * Kstage n = Kstage n * S_left n)
    (n : ℕ) :
    limitElement S_left * limitK Kstage = limitK Kstage * limitElement S_left :=
  compatible_limit_commute S_left Kstage hS hK hcomm n

/-! ## Offset local phase axis, starting at the first nontrivial tower stage -/

/-- The local real phase-axis matrix on one `Cl(1,1)` matrix factor. -/
@[rep_depth operator]
def phaseAxisMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- The local phase-axis matrix squares to `-1`. -/
@[rep_depth operator]
theorem phaseAxisMatrix_sq :
    phaseAxisMatrix * phaseAxisMatrix = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseAxisMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/--
The first nontrivial tower-stage phase axis.

`Stage 0` is scalar, so the local `Cl(1,1)` atom starts at `Stage 1`.
-/
@[rep_depth operator]
def localPhaseAxis : TowerStage 1 :=
  (1 : TowerStage 0) ⊗ₖ phaseAxisMatrix

/--
The transported local phase-axis sequence beginning at `Stage 1`.

The element at stage `k + 1` is obtained by repeatedly applying the tower
bonding map to the local phase axis.
-/
@[rep_depth operator]
def stageKFromOne : (k : ℕ) → TowerStage (k + 1)
  | 0 => localPhaseAxis
  | k + 1 => stageEmbed (k + 1) (stageKFromOne k)

/-- The transported local phase-axis sequence is compatible with the bonding maps. -/
@[rep_depth operator]
theorem stageKFromOne_commutes_bond (k : ℕ) :
    stageEmbed (k + 1) (stageKFromOne k) = stageKFromOne (k + 1) :=
  rfl

/-- The direct-limit element represented by stage one of a compatible offset sequence. -/
@[rep_depth operator]
def limitElementFromOne (F : ∀ k : ℕ, TowerStage (k + 1)) : TowerLimit :=
  ofStage 1 (F 0)

/--
Any compatible sequence starting at `Stage 1` has a stage-independent
direct-limit image.
-/
@[rep_depth operator]
theorem limitElementFromOne_eq_stage
    (F : ∀ k : ℕ, TowerStage (k + 1))
    (hF : ∀ k : ℕ, stageEmbed (k + 1) (F k) = F (k + 1))
    (k : ℕ) :
    ofStage (k + 1) (F k) = limitElementFromOne F := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [← hF k]
      rw [ofStage_apply_bond (k + 1) (F k)]
      exact ih

/-- The colimit phase axis represented by the local `Stage 1` phase axis. -/
@[rep_depth operator]
def limitKFromOne : TowerLimit :=
  limitElementFromOne stageKFromOne

/-- The transported local phase axis has a stage-independent colimit image. -/
@[rep_depth operator]
theorem limitKFromOne_wellDefined (k : ℕ) :
    ofStage (k + 1) (stageKFromOne k) = limitKFromOne :=
  limitElementFromOne_eq_stage stageKFromOne stageKFromOne_commutes_bond k

@[rep_depth operator]
theorem stageKFromOne_sq (k : ℕ) :
    stageKFromOne k * stageKFromOne k =
      -(1 : TowerStage (k + 1)) := by
  induction k with
  | zero =>
      change localPhaseAxis * localPhaseAxis = -(1 : TowerStage 1)
      change ((1 : TowerStage 0) ⊗ₖ phaseAxisMatrix) *
        ((1 : TowerStage 0) ⊗ₖ phaseAxisMatrix) =
        -(1 : TowerStage 1)
      rw [← Matrix.mul_kronecker_mul]
      rw [phaseAxisMatrix_sq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
      change stageEmbed (k + 1) (stageKFromOne k) *
        stageEmbed (k + 1) (stageKFromOne k) =
        -(1 : TowerStage (k + 2))
      rw [← map_mul]
      rw [ih]
      simpa only [map_neg, map_one]

@[rep_depth operator]
theorem limitKFromOne_sq :
    limitKFromOne * limitKFromOne = -(1 : TowerLimit) := by
  rw [← limitKFromOne_wellDefined 0]
  rw [← ofStage_mul, stageKFromOne_sq, ofStage_neg, ofStage_one]

/--
Compatible offset finite-stage representatives that commute at every stage have
commuting images in the direct limit.
-/
@[rep_depth operator]
theorem compatible_limit_commute_from_one
    (A B : ∀ k : ℕ, TowerStage (k + 1))
    (hA : ∀ k : ℕ, stageEmbed (k + 1) (A k) = A (k + 1))
    (hB : ∀ k : ℕ, stageEmbed (k + 1) (B k) = B (k + 1))
    (hcomm : ∀ k : ℕ, A k * B k = B k * A k)
    (k : ℕ) :
    limitElementFromOne A * limitElementFromOne B =
      limitElementFromOne B * limitElementFromOne A := by
  calc
    limitElementFromOne A * limitElementFromOne B
        = ofStage (k + 1) (A k) * ofStage (k + 1) (B k) := by
            rw [← limitElementFromOne_eq_stage A hA k,
              ← limitElementFromOne_eq_stage B hB k]
    _ = ofStage (k + 1) (B k) * ofStage (k + 1) (A k) := by
            exact limit_commute (n := k + 1) (hcomm k)
    _ = limitElementFromOne B * limitElementFromOne A := by
            rw [limitElementFromOne_eq_stage B hB k,
              limitElementFromOne_eq_stage A hA k]

/--
Offset Path-2 Cuntz/K commutation theorem.

If a finite-stage Cuntz left branch is compatible from `Stage 1` onward and
commutes at every stage with the transported local phase axis, then its colimit
image commutes with `limitKFromOne`.
-/
@[rep_depth operator]
theorem S_left_commutes_K_limit_from_one
    (S_left : ∀ k : ℕ, TowerStage (k + 1))
    (hS : ∀ k : ℕ, stageEmbed (k + 1) (S_left k) = S_left (k + 1))
    (hcomm : ∀ k : ℕ, S_left k * stageKFromOne k = stageKFromOne k * S_left k)
    (k : ℕ) :
    limitElementFromOne S_left * limitKFromOne =
      limitKFromOne * limitElementFromOne S_left :=
  compatible_limit_commute_from_one
    S_left stageKFromOne hS stageKFromOne_commutes_bond hcomm k

end InfoGeometry.Canonical.CuntzKTowerCommutation
