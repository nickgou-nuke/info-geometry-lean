import InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge
import InfoGeometry.Clifford.G2Cl55ChiralEquivarianceBridge

/-!
# Finite `G₂`--`Cl(5,5)` Hodge equivariance datum

This owner records the finite-dimensional operator package that is actually
available in the repository.  It is deliberately a datum, not a claim that a
full analytic or equivariant `KK`-class has been constructed: bounded
transforms, compactness, and Kasparov products require additional analytic
interfaces.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2Cl55FiniteHodgeEquivarianceDatum

open Matrix
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Clifford.G2Cl55ChiralEquivarianceBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32
abbrev Derivation := SplitOctonionDerivationSpinorLiftBridge.Derivation

/-- The finite operator datum carried by a Lie action on the master spinor
carrier.  The two commutation fields are the exact equivariance hypotheses;
the Hodge operator itself is the canonical finite owner operator. -/
structure FiniteG2HodgeDatum where
  action : Derivation →ₗ⁅ℝ⁆ Mat32
  action_even : ∀ D,
    action D * MasterChirality = MasterChirality * action D
  action_hodge : ∀ D,
    action D * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * action D

/-! ## Finite Fredholm/Kasparov-style phase socket

This is intentionally an algebraic finite-dimensional socket.  It records the
phase, grading, oddness, and equivariance laws which are available here, but it
does not assert compactness, completeness, or an analytic `KK`-class.
-/

structure FiniteKasparovPhaseDatum where
  phase : Mat32
  grading : Mat32
  action : Derivation →ₗ⁅ℝ⁆ Mat32
  phase_square : phase * phase = (1 : Mat32)
  grading_square : grading * grading = (1 : Mat32)
  phase_transpose : phaseᵀ = phase
  grading_transpose : gradingᵀ = grading
  phase_odd : grading * phase + phase * grading = 0
  action_even : ∀ D, action D * grading = grading * action D
  action_phase : ∀ D, action D * phase = phase * action D

variable (F : FiniteKasparovPhaseDatum)

theorem phase_is_involution : F.phase * F.phase = (1 : Mat32) := F.phase_square

theorem grading_is_involution : F.grading * F.grading = (1 : Mat32) :=
  F.grading_square

theorem phase_is_grading_odd :
    F.grading * F.phase + F.phase * F.grading = 0 := F.phase_odd

theorem phase_action_commutes (D : Derivation) :
    F.action D * F.phase = F.phase * F.action D := F.action_phase D

theorem grading_action_commutes (D : Derivation) :
    F.action D * F.grading = F.grading * F.action D := F.action_even D

variable (K : FiniteG2HodgeDatum)

theorem action_commutes_masterChirality (D : Derivation) :
    K.action D * MasterChirality = MasterChirality * K.action D :=
  K.action_even D

theorem action_commutes_hodge (D : Derivation) :
    K.action D * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * K.action D :=
  K.action_hodge D

/-! A native Clifford lift now feeds directly into the finite Hodge datum.
The lift itself remains an explicit input; this adapter only composes the
already-proved native Lie and covariance interfaces. -/

def finiteG2HodgeDatumOfNativeLift
    (N : NativeSpinorLiftDatum) : FiniteG2HodgeDatum where
  action := nativeDerivationSpinorLieHom N
  action_even := by
    intro D
    exact nativeDerivationSpinorAction_commutes_chirality N D
  action_hodge := by
    intro D
    exact nativeDerivationSpinorAction_commutes_hodge N D

@[simp] theorem finiteG2HodgeDatumOfNativeLift_action
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    (finiteG2HodgeDatumOfNativeLift N).action D =
      nativeDerivationSpinorAction N D := rfl

theorem finiteG2HodgeDatumOfNativeLift_action_even
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    (finiteG2HodgeDatumOfNativeLift N).action D * MasterChirality =
      MasterChirality * (finiteG2HodgeDatumOfNativeLift N).action D := by
  exact (finiteG2HodgeDatumOfNativeLift N).action_even D

theorem finiteG2HodgeDatumOfNativeLift_action_hodge
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    (finiteG2HodgeDatumOfNativeLift N).action D * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac *
        (finiteG2HodgeDatumOfNativeLift N).action D := by
  exact (finiteG2HodgeDatumOfNativeLift N).action_hodge D

theorem action_preserves_chiralPlus (D : Derivation) :
    K.action D * masterChiralProjectorPlus =
      masterChiralProjectorPlus * K.action D := by
  rw [masterChiralProjectorPlus, Algebra.mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, action_commutes_masterChirality K D]
  simp only [mul_one, one_mul]

theorem action_preserves_chiralMinus (D : Derivation) :
    K.action D * masterChiralProjectorMinus =
      masterChiralProjectorMinus * K.action D := by
  rw [masterChiralProjectorMinus, Algebra.mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, action_commutes_masterChirality K D]
  simp only [mul_one, one_mul]

theorem hodge_is_chirality_odd :
    MasterChirality * embeddedSplitOctonionHodgeDirac +
      embeddedSplitOctonionHodgeDirac * MasterChirality = 0 :=
  masterChirality_anticomm_hodge

theorem hodge_square :
    embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac =
      (3 : ℝ) • (1 : Mat32) :=
  embeddedSplitOctonionHodgeDirac_sq

/-- Finite normalized Hodge phase.  This is the algebraic normalization of
the finite operator with square `3I`; it is not an analytic unbounded
Baaj--Julg transform. -/
noncomputable def normalizedHodgePhase : Mat32 :=
  (1 / Real.sqrt 3 : ℝ) • embeddedSplitOctonionHodgeDirac

theorem sqrt_three_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
  have h : (0 : ℝ) ≤ 3 := by norm_num
  exact Real.sq_sqrt h

theorem normalizedHodgePhase_sq :
    normalizedHodgePhase * normalizedHodgePhase = (1 : Mat32) := by
  unfold normalizedHodgePhase
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hodge_square]
  have hs : (Real.sqrt 3 : ℝ) ≠ 0 := by positivity
  have hs2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := sqrt_three_sq
  rw [smul_smul]
  have hc : (1 / (Real.sqrt 3 : ℝ)) * (1 / (Real.sqrt 3 : ℝ)) * 3 = 1 := by
    field_simp [hs, hs2]
    exact hs2.symm
  rw [hc, one_smul]

theorem normalizedHodgePhase_is_chirality_odd :
    MasterChirality * normalizedHodgePhase +
      normalizedHodgePhase * MasterChirality = 0 := by
  unfold normalizedHodgePhase
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, hodge_is_chirality_odd,
    smul_zero]

theorem normalizedHodgePhase_transpose :
    normalizedHodgePhaseᵀ = normalizedHodgePhase := by
  unfold normalizedHodgePhase
  rw [Matrix.transpose_smul, embeddedSplitOctonionHodgeDirac_transpose]

theorem action_commutes_normalizedHodgePhase (D : Derivation) :
    K.action D * normalizedHodgePhase =
      normalizedHodgePhase * K.action D := by
  unfold normalizedHodgePhase
  rw [mul_smul_comm, smul_mul_assoc, action_commutes_hodge K D]

/-- The normalized finite Hodge phase packaged as an algebraic
Fredholm/Kasparov-style datum.  The construction is finite and exact:
`phase² = 1`; no analytic bounded-transform or compactness claim is made. -/
def toFiniteKasparovPhase (K : FiniteG2HodgeDatum) : FiniteKasparovPhaseDatum where
  phase := normalizedHodgePhase
  grading := MasterChirality
  action := K.action
  phase_square := normalizedHodgePhase_sq
  grading_square := by
    simpa using masterChirality_sq
  phase_transpose := normalizedHodgePhase_transpose
  grading_transpose := masterChirality_transpose
  phase_odd := normalizedHodgePhase_is_chirality_odd
  action_even := K.action_even
  action_phase := fun D => action_commutes_normalizedHodgePhase K D

/-! Direct composition for native lifts.  This is still a finite algebraic
certificate; it deliberately does not assert an analytic Kasparov class. -/

def finiteKasparovPhaseOfNativeLift
    (N : NativeSpinorLiftDatum) : FiniteKasparovPhaseDatum :=
  toFiniteKasparovPhase (finiteG2HodgeDatumOfNativeLift N)

@[simp] theorem finiteKasparovPhaseOfNativeLift_phase
    (N : NativeSpinorLiftDatum) :
    (finiteKasparovPhaseOfNativeLift N).phase = normalizedHodgePhase := rfl

@[simp] theorem finiteKasparovPhaseOfNativeLift_grading
    (N : NativeSpinorLiftDatum) :
    (finiteKasparovPhaseOfNativeLift N).grading = MasterChirality := rfl

theorem finiteKasparovPhaseOfNativeLift_phase_square
    (N : NativeSpinorLiftDatum) :
    (finiteKasparovPhaseOfNativeLift N).phase *
        (finiteKasparovPhaseOfNativeLift N).phase = (1 : Mat32) := by
  exact (finiteKasparovPhaseOfNativeLift N).phase_square

theorem finiteKasparovPhaseOfNativeLift_phase_odd
    (N : NativeSpinorLiftDatum) :
    MasterChirality * (finiteKasparovPhaseOfNativeLift N).phase +
        (finiteKasparovPhaseOfNativeLift N).phase * MasterChirality = 0 := by
  simpa [finiteKasparovPhaseOfNativeLift] using
    normalizedHodgePhase_is_chirality_odd

theorem finiteKasparovPhaseOfNativeLift_action_phase
    (N : NativeSpinorLiftDatum) (D : Derivation) :
    (finiteKasparovPhaseOfNativeLift N).action D *
        (finiteKasparovPhaseOfNativeLift N).phase =
      (finiteKasparovPhaseOfNativeLift N).phase *
        (finiteKasparovPhaseOfNativeLift N).action D := by
  exact (finiteKasparovPhaseOfNativeLift N).action_phase D

@[simp] theorem toFiniteKasparovPhase_phase (K : FiniteG2HodgeDatum) :
    (toFiniteKasparovPhase K).phase = normalizedHodgePhase := rfl

@[simp] theorem toFiniteKasparovPhase_grading (K : FiniteG2HodgeDatum) :
    (toFiniteKasparovPhase K).grading = MasterChirality := rfl

theorem toFiniteKasparovPhase_is_finite_involution (K : FiniteG2HodgeDatum) :
    (toFiniteKasparovPhase K).phase *
        (toFiniteKasparovPhase K).phase = (1 : Mat32) :=
  (toFiniteKasparovPhase K).phase_square

theorem toFiniteKasparovPhase_is_equivariant (K : FiniteG2HodgeDatum)
    (D : Derivation) :
    (toFiniteKasparovPhase K).action D *
        (toFiniteKasparovPhase K).phase =
      (toFiniteKasparovPhase K).phase *
        (toFiniteKasparovPhase K).action D :=
  (toFiniteKasparovPhase K).action_phase D

theorem normalizedHodgePhase_defect_zero :
    (1 : Mat32) - normalizedHodgePhase * normalizedHodgePhase = 0 := by
  rw [normalizedHodgePhase_sq, sub_self]

theorem normalizedHodgePhase_intertwines_chiralPlus :
    normalizedHodgePhase * masterChiralProjectorPlus =
      masterChiralProjectorMinus * normalizedHodgePhase := by
  unfold normalizedHodgePhase
  rw [smul_mul_assoc, mul_smul_comm, masterHodgeDirac_comp_projectorPlus]

theorem normalizedHodgePhase_intertwines_chiralMinus :
    normalizedHodgePhase * masterChiralProjectorMinus =
      masterChiralProjectorPlus * normalizedHodgePhase := by
  unfold normalizedHodgePhase
  rw [smul_mul_assoc, mul_smul_comm, masterHodgeDirac_comp_projectorMinus]

def normalizedHodgeKernel : Set (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ) :=
  {v | normalizedHodgePhase.mulVec v = 0}

theorem action_preserves_normalizedHodgeKernel
    (D : Derivation) {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : v ∈ normalizedHodgeKernel) :
    (K.action D).mulVec v ∈ normalizedHodgeKernel := by
  change normalizedHodgePhase.mulVec ((K.action D).mulVec v) = 0
  rw [Matrix.mulVec_mulVec]
  rw [← action_commutes_normalizedHodgePhase K D]
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem normalizedHodgeKernel_trivial
    {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : v ∈ normalizedHodgeKernel) :
    v = 0 := by
  change normalizedHodgePhase.mulVec v = 0 at hv
  have hsq := congrArg (fun M : Mat32 => M.mulVec v)
    (normalizedHodgePhase_sq)
  change (normalizedHodgePhase * normalizedHodgePhase).mulVec v =
    ((1 : Mat32)).mulVec v at hsq
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, Matrix.one_mulVec] at hsq
  exact hsq.symm

theorem normalizedHodgeKernel_eq_bot :
    normalizedHodgeKernel =
      ({0} : Set (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) := by
  ext v
  constructor
  · intro hv
    rw [normalizedHodgeKernel_trivial hv]
    simp
  · intro hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    simp [normalizedHodgeKernel]

theorem hodge_intertwines_chiralPlus :
    embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus =
      masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac :=
  masterHodgeDirac_comp_projectorPlus

theorem hodge_intertwines_chiralMinus :
    embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus =
      masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac :=
  masterHodgeDirac_comp_projectorMinus

/-- The finite Hodge kernel is invariant under the packaged Lie action. -/
def hodgeKernel : Set (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ) :=
  {v | embeddedSplitOctonionHodgeDirac.mulVec v = 0}

theorem action_preserves_hodgeKernel
    (D : Derivation) {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : v ∈ hodgeKernel) :
    (K.action D).mulVec v ∈ hodgeKernel := by
  change embeddedSplitOctonionHodgeDirac.mulVec
      ((K.action D).mulVec v) = 0
  rw [Matrix.mulVec_mulVec]
  rw [← action_commutes_hodge K D]
  rw [← Matrix.mulVec_mulVec]
  rw [hv, Matrix.mulVec_zero]

/-- The finite master Hodge operator has no zero modes: its square is the
nonzero scalar `3`, hence its kernel is trivial. -/
theorem hodge_kernel_trivial
    {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : v ∈ hodgeKernel) :
    v = 0 := by
  change embeddedSplitOctonionHodgeDirac.mulVec v = 0 at hv
  have hsq := congrArg
    (fun M : Mat32 => M.mulVec v) embeddedSplitOctonionHodgeDirac_sq
  change (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac).mulVec v =
    ((3 : ℝ) • (1 : Mat32)).mulVec v at hsq
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at hsq
  have hthree : (3 : ℝ) • v = 0 := by
    simpa [Matrix.smul_mulVec, Matrix.one_mulVec] using hsq.symm
  exact (smul_eq_zero.mp hthree).resolve_left (by norm_num)

theorem hodge_kernel_eq_bot : hodgeKernel = ({0} : Set (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) := by
  ext v
  constructor
  · intro hv
    rw [hodge_kernel_trivial hv]
    simp
  · intro hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    simp [hodgeKernel]

/-- Package a supplied native spinor lift as the finite equivariance datum.
The lift's Hodge and chirality compatibility remain explicit fields of the
native interface; no canonical `Derivation → SpinBivector55` map is invented.
-/
def ofNative (N : NativeSpinorLiftDatum) : FiniteG2HodgeDatum where
  action := nativeDerivationSpinorLieHom N
  action_even := nativeDerivationSpinorAction_commutes_chirality N
  action_hodge := nativeDerivationSpinorAction_commutes_hodge N

@[simp] theorem ofNative_action (N : NativeSpinorLiftDatum) (D : Derivation) :
    (ofNative N).action D = nativeDerivationSpinorAction N D := rfl

end InfoGeometry.Canonical.G2Cl55FiniteHodgeEquivarianceDatum
