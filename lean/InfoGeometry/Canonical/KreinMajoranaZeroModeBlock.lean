import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.ChiralKKTIsolation
import InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts

/-!
# InfoGeometry.Canonical.KreinMajoranaZeroModeBlock

Block-decomposition mechanism for a Krein/Majorana zero-mode lane, expressed in
the existing KKT corridor.

No wrappers. No `sorry`.
-/

namespace KreinMajoranaZeroModeBlock

open InfoGeometry.Canonical.KKTCore

section

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

noncomputable def zeroModeProjector (X : InfoGeometry.Quantum.RealSplitCl11Action H) : EndH :=
  plusProjector X

noncomputable def cozeroModeProjector (X : InfoGeometry.Quantum.RealSplitCl11Action H) : EndH :=
  minusProjector X

@[simp] theorem zeroModeProjector_idempotent
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) :
    zeroModeProjector X * zeroModeProjector X = zeroModeProjector X := by
  simpa [zeroModeProjector] using plusProjector_idempotent (X := X)

@[simp] theorem cozeroModeProjector_idempotent
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) :
    cozeroModeProjector X * cozeroModeProjector X = cozeroModeProjector X := by
  simpa [cozeroModeProjector] using minusProjector_idempotent (X := X)

@[simp] theorem zeroModeProjector_mul_cozeroModeProjector
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) :
    zeroModeProjector X * cozeroModeProjector X = 0 := by
  simpa [zeroModeProjector, cozeroModeProjector] using plusProjector_mul_minusProjector (X := X)

@[simp] theorem cozeroModeProjector_mul_zeroModeProjector
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) :
    cozeroModeProjector X * zeroModeProjector X = 0 := by
  simpa [zeroModeProjector, cozeroModeProjector] using minusProjector_mul_plusProjector (X := X)

theorem diagonal_block_decomposition_of_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    A = zeroModeProjector X * A * zeroModeProjector X
      + cozeroModeProjector X * A * cozeroModeProjector X := by
  simpa [zeroModeProjector, cozeroModeProjector] using
    eq_diagonal_blocks_of_isGZero (X := X) (A := A) hA

theorem off_block_vanish_of_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    zeroModeProjector X * A * cozeroModeProjector X = 0 ∧
    cozeroModeProjector X * A * zeroModeProjector X = 0 := by
  refine ⟨?_, ?_⟩
  · simpa [zeroModeProjector, cozeroModeProjector] using
      plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero (X := X) (A := A) hA
  · simpa [zeroModeProjector, cozeroModeProjector] using
      minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero (X := X) (A := A) hA

theorem uPlus_zeroMode_diagonal_vanish
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A : EndH) :
    zeroModeProjector X * uPlus X A * zeroModeProjector X = 0 := by
  unfold zeroModeProjector uPlus gOnePart
  rw [mul_assoc, mul_assoc]
  rw [minusProjector_mul_plusProjector]
  simp

theorem uMinus_cozeroMode_diagonal_vanish
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A : EndH) :
    cozeroModeProjector X * uMinus X A * cozeroModeProjector X = 0 := by
  unfold cozeroModeProjector uMinus gNegOnePart
  rw [mul_assoc, mul_assoc]
  rw [plusProjector_mul_minusProjector]
  simp

theorem polarized_commutator_block_diagonal
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH) :
    commutator (uPlus X A) (uMinus X B)
      = zeroModeProjector X * commutator (uPlus X A) (uMinus X B) * zeroModeProjector X
        + cozeroModeProjector X * commutator (uPlus X A) (uMinus X B) * cozeroModeProjector X := by
  have hG0 : IsGZero X (commutator (uPlus X A) (uMinus X B)) :=
    commutator_uPlus_uMinus_isGZero (X := X) A B
  simpa [zeroModeProjector, cozeroModeProjector] using
    eq_diagonal_blocks_of_isGZero (X := X)
      (A := commutator (uPlus X A) (uMinus X B)) hG0

noncomputable def zeroModePart
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A : EndH) : EndH :=
  zeroModeProjector X * A * zeroModeProjector X

noncomputable def cozeroModePart
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A : EndH) : EndH :=
  cozeroModeProjector X * A * cozeroModeProjector X

theorem polarized_commutator_reconstruct_from_blocks
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH) :
    commutator (uPlus X A) (uMinus X B)
      = zeroModePart X (commutator (uPlus X A) (uMinus X B))
        + cozeroModePart X (commutator (uPlus X A) (uMinus X B)) := by
  simpa [zeroModePart, cozeroModePart] using
    polarized_commutator_block_diagonal (X := X) A B

theorem polarized_commutator_off_blocks_zero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH) :
    zeroModeProjector X * commutator (uPlus X A) (uMinus X B) * cozeroModeProjector X = 0 ∧
    cozeroModeProjector X * commutator (uPlus X A) (uMinus X B) * zeroModeProjector X = 0 := by
  have hG0 : IsGZero X (commutator (uPlus X A) (uMinus X B)) :=
    commutator_uPlus_uMinus_isGZero (X := X) A B
  exact off_block_vanish_of_isGZero (X := X) (A := commutator (uPlus X A) (uMinus X B)) hG0

theorem boost_block_diagonal_preserves_zero_mode
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {B : EndH}
    (hB : IsGZero X B) :
    zeroModeProjector X * B = zeroModeProjector X * B * zeroModeProjector X := by
  have hOff : zeroModeProjector X * B * cozeroModeProjector X = 0 :=
    (off_block_vanish_of_isGZero (X := X) (A := B) hB).1
  have hsum : zeroModeProjector X + cozeroModeProjector X = (1 : EndH) := by
    simpa [zeroModeProjector, cozeroModeProjector] using plusProjector_add_minusProjector (X := X)
  calc
    zeroModeProjector X * B
        = zeroModeProjector X * B * (1 : EndH) := by simp
    _ = zeroModeProjector X * B * (zeroModeProjector X + cozeroModeProjector X) := by rw [hsum]
    _ = zeroModeProjector X * B * zeroModeProjector X
          + zeroModeProjector X * B * cozeroModeProjector X := by
            simp [mul_add, mul_assoc]
    _ = zeroModeProjector X * B * zeroModeProjector X := by simp [hOff]

theorem boost_block_diagonal_preserves_zero_mode_right
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {B : EndH}
    (hB : IsGZero X B) :
    B * zeroModeProjector X = zeroModeProjector X * B * zeroModeProjector X := by
  have hOffR : cozeroModeProjector X * B * zeroModeProjector X = 0 :=
    (off_block_vanish_of_isGZero (X := X) (A := B) hB).2
  have hsum : zeroModeProjector X + cozeroModeProjector X = (1 : EndH) := by
    simpa [zeroModeProjector, cozeroModeProjector] using plusProjector_add_minusProjector (X := X)
  calc
    B * zeroModeProjector X
        = (1 : EndH) * B * zeroModeProjector X := by simp
    _ = (zeroModeProjector X + cozeroModeProjector X) * B * zeroModeProjector X := by rw [hsum]
    _ = zeroModeProjector X * B * zeroModeProjector X
          + cozeroModeProjector X * B * zeroModeProjector X := by
            simp [add_mul, mul_assoc]
    _ = zeroModeProjector X * B * zeroModeProjector X := by simp [hOffR]

theorem anomaly_restriction_theorem
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {chi : EndH}
    (hchi : IsGZero X chi) :
    ∃ chi0 chic : EndH,
      chi0 = zeroModeProjector X * chi * zeroModeProjector X ∧
      chic = cozeroModeProjector X * chi * cozeroModeProjector X ∧
      chi = chi0 + chic ∧
      zeroModeProjector X * chi * cozeroModeProjector X = 0 ∧
      cozeroModeProjector X * chi * zeroModeProjector X = 0 := by
  refine ⟨zeroModePart X chi, cozeroModePart X chi, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [zeroModePart, cozeroModePart] using
      diagonal_block_decomposition_of_isGZero (X := X) (A := chi) hchi
  · exact (off_block_vanish_of_isGZero (X := X) (A := chi) hchi).1
  · exact (off_block_vanish_of_isGZero (X := X) (A := chi) hchi).2

/--
Any grade-zero channel commutes with the zero-mode projector.
-/
theorem zeroModeProjector_commutes_of_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    zeroModeProjector X * A = A * zeroModeProjector X := by
  rw [boost_block_diagonal_preserves_zero_mode (X := X) (B := A) hA]
  rw [boost_block_diagonal_preserves_zero_mode_right (X := X) (B := A) hA]

/--
Any grade-zero channel commutes with the complementary projector.
-/
theorem cozeroModeProjector_commutes_of_isGZero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    cozeroModeProjector X * A = A * cozeroModeProjector X := by
  have hsum : zeroModeProjector X + cozeroModeProjector X = (1 : EndH) := by
    simpa [zeroModeProjector, cozeroModeProjector] using plusProjector_add_minusProjector (X := X)
  have hL : zeroModeProjector X * A = A * zeroModeProjector X :=
    zeroModeProjector_commutes_of_isGZero (X := X) (A := A) hA
  apply add_left_cancel (a := zeroModeProjector X * A)
  calc
    zeroModeProjector X * A + cozeroModeProjector X * A
        = (zeroModeProjector X + cozeroModeProjector X) * A := by simp [add_mul]
    _ = A := by simp [hsum]
    _ = A * (zeroModeProjector X + cozeroModeProjector X) := by simp [hsum]
    _ = A * zeroModeProjector X + A * cozeroModeProjector X := by simp [mul_add]
    _ = zeroModeProjector X * A + A * cozeroModeProjector X := by simpa [hL]

theorem block_normal_form_of_off_blocks_zero
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A : EndH)
    (hpm : zeroModeProjector X * A * cozeroModeProjector X = 0)
    (hmp : cozeroModeProjector X * A * zeroModeProjector X = 0) :
    A = zeroModePart X A + cozeroModePart X A := by
  have hsum : zeroModeProjector X + cozeroModeProjector X = (1 : EndH) := by
    simpa [zeroModeProjector, cozeroModeProjector] using plusProjector_add_minusProjector (X := X)
  calc
    A = (zeroModeProjector X + cozeroModeProjector X) * A * (zeroModeProjector X + cozeroModeProjector X) := by
          simp [hsum]
    _ = zeroModeProjector X * A * zeroModeProjector X
          + zeroModeProjector X * A * cozeroModeProjector X
          + (cozeroModeProjector X * A * zeroModeProjector X
              + cozeroModeProjector X * A * cozeroModeProjector X) := by
            simp [mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm]
    _ = zeroModeProjector X * A * zeroModeProjector X
          + (cozeroModeProjector X * A * zeroModeProjector X
              + cozeroModeProjector X * A * cozeroModeProjector X) := by
            simp [hpm]
    _ = zeroModeProjector X * A * zeroModeProjector X
          + cozeroModeProjector X * A * cozeroModeProjector X := by
          simp [hmp]
    _ = zeroModePart X A + cozeroModePart X A := rfl

theorem polarized_commutator_block_normal_form
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH) :
    commutator (uPlus X A) (uMinus X B)
      = zeroModePart X (commutator (uPlus X A) (uMinus X B))
        + cozeroModePart X (commutator (uPlus X A) (uMinus X B)) := by
  rcases polarized_commutator_off_blocks_zero (X := X) A B with ⟨hpm, hmp⟩
  exact block_normal_form_of_off_blocks_zero
    (X := X) (A := commutator (uPlus X A) (uMinus X B)) hpm hmp

/--
If the doubled zero/cozero blocks of a grade-zero anomaly are particle-hole
opposites, the total anomaly cancels.

This is only the finite algebraic cancellation law. It does not assert an
analytic condensate, a physical boundary state, or topological protection.
-/
theorem paired_block_anomaly_cancel
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {chi : EndH}
    (hchi : IsGZero X chi)
    (hpair : cozeroModePart X chi = -zeroModePart X chi) :
    chi = 0 := by
  calc
    chi = zeroModePart X chi + cozeroModePart X chi := by
      simpa [zeroModePart, cozeroModePart] using
        diagonal_block_decomposition_of_isGZero (X := X) (A := chi) hchi
    _ = zeroModePart X chi + -zeroModePart X chi := by rw [hpair]
    _ = 0 := by simp

/--
The zero total anomaly has opposite zero/cozero blocks.
-/
theorem paired_blocks_of_anomaly_cancel
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {chi : EndH}
    (hzero : chi = 0) :
    cozeroModePart X chi = -zeroModePart X chi := by
  subst chi
  simp [zeroModePart, cozeroModePart]

/--
For a grade-zero doubled anomaly, cancellation is equivalent to particle-hole
opposition of the two diagonal blocks.
-/
theorem paired_block_anomaly_cancel_iff
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) {chi : EndH}
    (hchi : IsGZero X chi) :
    chi = 0 ↔ cozeroModePart X chi = -zeroModePart X chi := by
  constructor
  · exact paired_blocks_of_anomaly_cancel (X := X)
  · exact paired_block_anomaly_cancel (X := X) hchi

/--
The polarized `uPlus/uMinus` commutator anomaly cancels when its zero/cozero
Majorana blocks are particle-hole opposites.
-/
theorem polarized_commutator_cancel_of_paired_blocks
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (hpair :
      cozeroModePart X (commutator (uPlus X A) (uMinus X B)) =
        -zeroModePart X (commutator (uPlus X A) (uMinus X B))) :
    commutator (uPlus X A) (uMinus X B) = 0 :=
  paired_block_anomaly_cancel (X := X)
    (hchi := commutator_uPlus_uMinus_isGZero (X := X) A B)
    hpair

/--
For the polarized `uPlus/uMinus` channel, zero total anomaly is equivalent to
particle-hole opposition of the extracted zero/cozero blocks.
-/
theorem polarized_commutator_cancel_iff_paired_blocks
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH) :
    commutator (uPlus X A) (uMinus X B) = 0 ↔
      cozeroModePart X (commutator (uPlus X A) (uMinus X B)) =
        -zeroModePart X (commutator (uPlus X A) (uMinus X B)) :=
  paired_block_anomaly_cancel_iff (X := X)
    (hchi := commutator_uPlus_uMinus_isGZero (X := X) A B)

/--
Projector commutation specialized to the polarized mixed commutator channel.
-/
theorem polarized_commutator_commutes_zeroModeProjector
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH) :
    zeroModeProjector X * commutator (uPlus X A) (uMinus X B)
      = commutator (uPlus X A) (uMinus X B) * zeroModeProjector X := by
  exact zeroModeProjector_commutes_of_isGZero (X := X)
    (A := commutator (uPlus X A) (uMinus X B))
    (commutator_uPlus_uMinus_isGZero (X := X) A B)

/--
Finite witness bridge: if the extracted zero-mode polarized channel is modeled
by a skew Pfaffian kernel, then the Pfaffian amplitude squares to the
determinant shadow of that extracted block.
-/
theorem zeroMode_polarized_pfaffian_sq_eq_det_shadow
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (hModel :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega) :
    P.pfaffian * P.pfaffian =
      (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det := by
  rw [hModel]
  exact P.pf_sq_eq_det

/--
Finite source--sink bridge: if a determinant path-count kernel is identified
with the same extracted zero-mode polarized block model, its determinant count
agrees with the Pfaffian-square shadow.
-/
theorem zeroMode_polarized_detCount_eq_pfaffian_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    D.detCount = P.pfaffian * P.pfaffian := by
  calc
    D.detCount
        = (InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix
            D.kernel).det := D.detCount_eq_det
    _ = (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det := by
          rw [hKernel]
    _ = P.omega.det := by rw [hOmega]
    _ = P.pfaffian * P.pfaffian := by exact P.pf_sq_eq_det.symm

/--
Zero-mode criterion on the extracted polarized block:
the determinant shadow vanishes iff the Pfaffian amplitude vanishes.
-/
theorem zeroMode_polarized_det_shadow_zero_iff_pfaffian_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (hModel :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega) :
    (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det = 0
      ↔ P.pfaffian = 0 := by
  constructor
  · intro hdet
    have hsq : P.pfaffian * P.pfaffian = 0 := by
      calc
        P.pfaffian * P.pfaffian
            = (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det := by
                exact zeroMode_polarized_pfaffian_sq_eq_det_shadow
                  (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hModel
        _ = 0 := hdet
    exact mul_eq_zero.mp hsq |>.elim id id
  · intro hpf
    calc
      (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det
          = P.pfaffian * P.pfaffian := by
              exact (zeroMode_polarized_pfaffian_sq_eq_det_shadow
                (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hModel).symm
      _ = 0 := by simp [hpf]

/--
Equivalent criterion at source--sink count level:
if the determinant path count for the extracted block is zero, then the
Pfaffian amplitude is zero, and conversely.
-/
theorem zeroMode_polarized_detCount_zero_iff_pfaffian_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    D.detCount = 0 ↔ P.pfaffian = 0 := by
  constructor
  · intro hD
    have hEq : D.detCount = P.pfaffian * P.pfaffian :=
      zeroMode_polarized_detCount_eq_pfaffian_sq
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel
    have hsq : P.pfaffian * P.pfaffian = 0 := by simpa [hD] using hEq.symm
    exact mul_eq_zero.mp hsq |>.elim id id
  · intro hpf
    calc
      D.detCount = P.pfaffian * P.pfaffian :=
        zeroMode_polarized_detCount_eq_pfaffian_sq
          (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel
      _ = 0 := by simp [hpf]

/--
Nonnegativity of the determinant shadow for the extracted zero-mode polarized
block under a Pfaffian-kernel witness.
-/
theorem zeroMode_polarized_det_shadow_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (hModel :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega) :
    0 ≤ (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det := by
  calc
    0 ≤ P.pfaffian * P.pfaffian := by
      nlinarith [sq_nonneg P.pfaffian]
    _ = (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det := by
      exact zeroMode_polarized_pfaffian_sq_eq_det_shadow
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hModel

/--
Nonnegativity of the determinant path-count for the extracted zero-mode
polarized block, via the same Pfaffian witness.
-/
theorem zeroMode_polarized_detCount_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    0 ≤ D.detCount := by
  calc
    0 ≤ P.pfaffian * P.pfaffian := by
      nlinarith [sq_nonneg P.pfaffian]
    _ = D.detCount := by
      symm
      exact zeroMode_polarized_detCount_eq_pfaffian_sq
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel

/--
Strict positivity criterion for the determinant shadow of the extracted
zero-mode polarized block: positivity is equivalent to nonvanishing Pfaffian.
-/
theorem zeroMode_polarized_det_shadow_pos_iff_pfaffian_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (hModel :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega) :
    0 < (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det
      ↔ P.pfaffian ≠ 0 := by
  constructor
  · intro hpos
    intro hpf
    have hzero :
        (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det = 0 :=
      (zeroMode_polarized_det_shadow_zero_iff_pfaffian_zero
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hModel).2 hpf
    exact (lt_irrefl (0 : ℝ)) (hzero ▸ hpos)
  · intro hpf
    have hsq : 0 < P.pfaffian * P.pfaffian := by
      have hsq' : 0 < P.pfaffian ^ 2 := sq_pos_iff.mpr hpf
      simpa [sq] using hsq'
    rw [← zeroMode_polarized_pfaffian_sq_eq_det_shadow
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hModel]
    exact hsq

/--
Strict positivity criterion at determinant path-count level:
the count is strictly positive iff the Pfaffian amplitude is nonzero.
-/
theorem zeroMode_polarized_detCount_pos_iff_pfaffian_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    0 < D.detCount ↔ P.pfaffian ≠ 0 := by
  constructor
  · intro hpos hpf
    have hzero : D.detCount = 0 :=
      (zeroMode_polarized_detCount_zero_iff_pfaffian_zero
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel).2 hpf
    exact (lt_irrefl (0 : ℝ)) (hzero ▸ hpos)
  · intro hpf
    have hsq : 0 < P.pfaffian * P.pfaffian := by
      have hsq' : 0 < P.pfaffian ^ 2 := sq_pos_iff.mpr hpf
      simpa [sq] using hsq'
    rw [zeroMode_polarized_detCount_eq_pfaffian_sq
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel]
    exact hsq

/--
Direct zero-locus equivalence between determinant shadow of the extracted
zero-mode polarized block and the associated determinant path-count.
-/
theorem zeroMode_polarized_detCount_zero_iff_detShadow_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    D.detCount = 0
      ↔ (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det = 0 := by
  constructor
  · intro hD
    have hpf : P.pfaffian = 0 :=
      (zeroMode_polarized_detCount_zero_iff_pfaffian_zero
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel).1 hD
    exact (zeroMode_polarized_det_shadow_zero_iff_pfaffian_zero
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hOmega).2 hpf
  · intro hDet
    have hpf : P.pfaffian = 0 :=
      (zeroMode_polarized_det_shadow_zero_iff_pfaffian_zero
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hOmega).1 hDet
    exact (zeroMode_polarized_detCount_zero_iff_pfaffian_zero
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel).2 hpf

/--
Direct strict-positivity equivalence between determinant shadow of the extracted
zero-mode polarized block and the associated determinant path-count.
-/
theorem zeroMode_polarized_detCount_pos_iff_detShadow_pos
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    0 < D.detCount
      ↔ 0 < (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det := by
  constructor
  · intro hD
    have hpf : P.pfaffian ≠ 0 :=
      (zeroMode_polarized_detCount_pos_iff_pfaffian_ne_zero
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel).1 hD
    exact (zeroMode_polarized_det_shadow_pos_iff_pfaffian_ne_zero
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hOmega).2 hpf
  · intro hDet
    have hpf : P.pfaffian ≠ 0 :=
      (zeroMode_polarized_det_shadow_pos_iff_pfaffian_ne_zero
        (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hOmega).1 hDet
    exact (zeroMode_polarized_detCount_pos_iff_pfaffian_ne_zero
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel).2 hpf

/--
Dirac/Pfaffian/zero-mode closure packet on the polarized `e+ / e-` channel.

Given explicit witnesses tying the extracted zero-mode mixed channel to a skew
Pfaffian kernel and to a source/sink determinant-count kernel, this theorem
packages the three owner-side facts:
1. the channel has a Pfaffian amplitude (`P.pfaffian`),
2. its square equals the determinant shadow of that block,
3. the same square equals the source/sink determinant count.
-/
theorem polarized_zeroMode_pfaffian_loop_packet
    {I : Type*} [Fintype I] [DecidableEq I]
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) (A B : EndH)
    (toMatrix : EndH → Matrix I I ℝ)
    (P : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.PfaffianKernel I)
    (D : InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.DeterminantPathCount I)
    (hOmega :
      toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B))) = P.omega)
    (hKernel :
      InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts.SourceSinkKernel.matrix D.kernel
        = toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))) :
    ∃ pf : ℝ,
      pf = P.pfaffian ∧
      pf * pf = (toMatrix (zeroModePart X (commutator (uPlus X A) (uMinus X B)))).det ∧
      D.detCount = pf * pf := by
  refine ⟨P.pfaffian, rfl, ?_, ?_⟩
  · exact zeroMode_polarized_pfaffian_sq_eq_det_shadow
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) hOmega
  · exact zeroMode_polarized_detCount_eq_pfaffian_sq
      (X := X) (A := A) (B := B) (toMatrix := toMatrix) (P := P) (D := D) hOmega hKernel

end

end KreinMajoranaZeroModeBlock
