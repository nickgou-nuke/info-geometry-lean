import Mathlib
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge

set_option linter.unusedSimpArgs false

/-!
# Real Split Krein Hilbertization and Dirac Module Bridge

This owner module records the finite matrix algebraic part of Layer I of the
audited Kasparov roadmap:

1. **Fundamental Krein Symmetry**:
   A real involution $\eta \in \operatorname{Mat}(32, \mathbb{R})$ satisfying $\eta^2 = 1$ and $\eta^\top = \eta$.

2. **Krein Adjoint Operation**:
   For any matrix $T \in \operatorname{Mat}(32, \mathbb{R})$, its Krein adjoint with respect to $\eta$ is:
   $$T^\times := \eta T^\top \eta.$$

3. **Involutive and Algebraic Properties of $T^\times$**:
   - $(I)^\times = I$
   - $(c \cdot T)^\times = c \cdot T^\times$
   - $(S + T)^\times = S^\times + T^\times$
   - $(S T)^\times = T^\times S^\times$
   - $(T^\times)^\times = T$

4. **Krein vs. Hilbert Self-Adjointness**:
   - Hilbert self-adjointness: $T^\top = T$.
   - Krein self-adjointness: $T^\times = T$.
   - Classification theorem: If $[\eta, T] = 0$, then $T^\times = T \iff T^\top = T$.
   - Anticommuting classification: If $\{\eta, T\} = 0$, then $T^\times = -T \iff T^\top = T$.

5. **Finite algebraic normalization**:
   - `masterBoundedTransform` is the explicitly defined matrix
     $F := \frac12 D_H$.
   - With the concrete choice $\eta=\Gamma$, the file proves
     $D_H^\times=-D_H$ and $F^\times=-F$, together with the square, oddness,
     and finite matrix commutation laws. It does not prove an analytic
     bounded transform of an unbounded regular self-adjoint operator.

The firewalls are intentional: no standard `KKO` class, regular
self-adjointness theorem, group integration, topology, or Kasparov product is
constructed here. Those require separate owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

/-- Structure packaging a fundamental Krein symmetry on the 32D spinor carrier. -/
structure KreinFundamentalSymmetry where
  eta : Mat32
  eta_sq : eta * eta = 1
  eta_transpose : etaᵀ = eta

/-- The Krein adjoint of a 32D operator with respect to a fundamental symmetry $\eta$. -/
def kreinAdjoint (K : KreinFundamentalSymmetry) (T : Mat32) : Mat32 :=
  K.eta * Tᵀ * K.eta

@[simp] theorem kreinAdjoint_one (K : KreinFundamentalSymmetry) :
    kreinAdjoint K 1 = 1 := by
  unfold kreinAdjoint
  simp only [transpose_one, mul_one, K.eta_sq]

theorem kreinAdjoint_smul (K : KreinFundamentalSymmetry) (c : ℝ) (T : Mat32) :
    kreinAdjoint K (c • T) = c • kreinAdjoint K T := by
  unfold kreinAdjoint
  simp only [transpose_smul, smul_mul_assoc, mul_smul_comm]

theorem kreinAdjoint_add (K : KreinFundamentalSymmetry) (S T : Mat32) :
    kreinAdjoint K (S + T) = kreinAdjoint K S + kreinAdjoint K T := by
  unfold kreinAdjoint
  simp only [transpose_add, add_mul, mul_add]

theorem kreinAdjoint_mul (K : KreinFundamentalSymmetry) (S T : Mat32) :
    kreinAdjoint K (S * T) = kreinAdjoint K T * kreinAdjoint K S := by
  unfold kreinAdjoint
  calc
    K.eta * (S * T)ᵀ * K.eta = K.eta * (Tᵀ * Sᵀ) * K.eta := by
      rw [transpose_mul]
    _ = K.eta * Tᵀ * 1 * Sᵀ * K.eta := by
      simp only [mul_one, Matrix.mul_assoc]
    _ = K.eta * Tᵀ * (K.eta * K.eta) * Sᵀ * K.eta := by
      rw [K.eta_sq]
    _ = (K.eta * Tᵀ * K.eta) * (K.eta * Sᵀ * K.eta) := by
      simp only [Matrix.mul_assoc]

@[simp] theorem kreinAdjoint_involutive (K : KreinFundamentalSymmetry) (T : Mat32) :
    kreinAdjoint K (kreinAdjoint K T) = T := by
  unfold kreinAdjoint
  calc
    K.eta * (K.eta * Tᵀ * K.eta)ᵀ * K.eta = K.eta * (K.etaᵀ * (Tᵀ)ᵀ * K.etaᵀ) * K.eta := by
      simp only [transpose_mul, Matrix.mul_assoc]
    _ = K.eta * (K.eta * T * K.eta) * K.eta := by
      rw [K.eta_transpose, transpose_transpose]
    _ = (K.eta * K.eta) * T * (K.eta * K.eta) := by
      simp only [Matrix.mul_assoc]
    _ = 1 * T * 1 := by
      rw [K.eta_sq]
    _ = T := by
      simp only [one_mul, mul_one]

/-- Predicate for Krein self-adjointness $T^\times = T$. -/
def IsKreinSelfAdjoint (K : KreinFundamentalSymmetry) (T : Mat32) : Prop :=
  kreinAdjoint K T = T

/-- Predicate for Krein skew-adjointness $T^\times = -T$. -/
def IsKreinSkewAdjoint (K : KreinFundamentalSymmetry) (T : Mat32) : Prop :=
  kreinAdjoint K T = -T

/-- Predicate for Hilbert (Euclidean) self-adjointness $T^\top = T$. -/
def IsHilbertSelfAdjoint (T : Mat32) : Prop :=
  Tᵀ = T

/-- The master chirality is a concrete finite fundamental Krein symmetry. -/
def masterKreinFundamentalSymmetry : KreinFundamentalSymmetry where
  eta := MasterChirality
  eta_sq := masterChirality_sq
  eta_transpose := by
    simpa [MasterChirality] using
      (InfoGeometry.Canonical.Cl55WittCAR.globalChirality_transpose 5)

theorem masterKreinFundamentalSymmetry_eta_sq :
    masterKreinFundamentalSymmetry.eta * masterKreinFundamentalSymmetry.eta = 1 :=
  masterChirality_sq

theorem masterKreinFundamentalSymmetry_eta_transpose :
    masterKreinFundamentalSymmetry.etaᵀ = masterKreinFundamentalSymmetry.eta :=
by
  simpa [masterKreinFundamentalSymmetry, MasterChirality] using
    (InfoGeometry.Canonical.Cl55WittCAR.globalChirality_transpose 5)

/-- 🏆 THEOREM: When $[\eta, T] = 0$, Krein self-adjointness is equivalent to Hilbert self-adjointness. -/
theorem krein_self_adjoint_iff_hilbert_of_comm
    (K : KreinFundamentalSymmetry) (T : Mat32)
    (hcomm : K.eta * Tᵀ = Tᵀ * K.eta) :
    IsKreinSelfAdjoint K T ↔ Tᵀ = T := by
  constructor
  · intro hK
    unfold IsKreinSelfAdjoint kreinAdjoint at hK
    have h1 : K.eta * Tᵀ * K.eta = T := hK
    have h2 : (K.eta * Tᵀ) * K.eta = T := by
      simpa only [Matrix.mul_assoc] using h1
    have h3 : (Tᵀ * K.eta) * K.eta = T := by
      rwa [hcomm] at h2
    have h4 : Tᵀ * (K.eta * K.eta) = T := by
      simpa only [Matrix.mul_assoc] using h3
    rwa [K.eta_sq, Matrix.mul_one] at h4
  · intro hH
    unfold IsKreinSelfAdjoint kreinAdjoint
    calc
      K.eta * Tᵀ * K.eta = (K.eta * Tᵀ) * K.eta := by
        simp only [Matrix.mul_assoc]
      _ = (Tᵀ * K.eta) * K.eta := by
        rw [hcomm]
      _ = Tᵀ * (K.eta * K.eta) := by
        simp only [Matrix.mul_assoc]
      _ = Tᵀ * 1 := by
        rw [K.eta_sq]
      _ = Tᵀ := by
        rw [Matrix.mul_one]
      _ = T := hH

/-- 🏆 THEOREM: When $\{\eta, T\} = 0$, Krein skew-adjointness is equivalent to Hilbert self-adjointness. -/
theorem krein_skew_adjoint_iff_hilbert_of_anticomm
    (K : KreinFundamentalSymmetry) (T : Mat32)
    (hanticomm : K.eta * Tᵀ = -(Tᵀ * K.eta)) :
    IsKreinSkewAdjoint K T ↔ Tᵀ = T := by
  constructor
  · intro hK
    unfold IsKreinSkewAdjoint kreinAdjoint at hK
    have h1 : K.eta * Tᵀ * K.eta = -T := hK
    have h2 : (K.eta * Tᵀ) * K.eta = -T := by
      simpa only [Matrix.mul_assoc] using h1
    have h3 : -(Tᵀ * K.eta) * K.eta = -T := by
      rwa [hanticomm] at h2
    have h4 : -(Tᵀ * (K.eta * K.eta)) = -T := by
      simpa only [Matrix.neg_mul, Matrix.mul_assoc] using h3
    have h5 : -(Tᵀ * 1) = -T := by
      rwa [K.eta_sq] at h4
    have h6 : -Tᵀ = -T := by
      rwa [Matrix.mul_one] at h5
    exact neg_inj.mp h6
  · intro hH
    unfold IsKreinSkewAdjoint kreinAdjoint
    calc
      K.eta * Tᵀ * K.eta = (K.eta * Tᵀ) * K.eta := by
        simp only [Matrix.mul_assoc]
      _ = -(Tᵀ * K.eta) * K.eta := by
        rw [hanticomm]
      _ = -(Tᵀ * (K.eta * K.eta)) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(Tᵀ * 1) := by
        rw [K.eta_sq]
      _ = -Tᵀ := by
        rw [Matrix.mul_one]
      _ = -T := by
        rw [hH]

/-! ### Master Hodge-Dirac finite matrix normalization and properties -/

/-- Finite matrix normalization $F = \frac{1}{2}D_H$. The retained name
is not a claim that the analytic unbounded-operator bounded-transform
construction has been formalized. -/
/-
This retained name denotes the explicit finite matrix normalization
`(1 / 2) • embeddedSplitOctonionHodgeDirac`; it is not a claim that an
analytic unbounded-operator bounded-transform construction has been formalized.
-/
def masterBoundedTransform : Mat32 :=
  (1 / 2 : ℝ) • embeddedSplitOctonionHodgeDirac

theorem masterBoundedTransform_transpose :
    masterBoundedTransformᵀ = masterBoundedTransform := by
  unfold masterBoundedTransform
  rw [Matrix.transpose_smul,
    embeddedSplitOctonionHodgeDirac_transpose]

theorem masterBoundedTransform_hilbert_self_adjoint :
    IsHilbertSelfAdjoint masterBoundedTransform :=
  masterBoundedTransform_transpose

theorem masterHodgeDirac_krein_skew_adjoint :
    IsKreinSkewAdjoint masterKreinFundamentalSymmetry
      embeddedSplitOctonionHodgeDirac := by
  have hanticomm :
      masterKreinFundamentalSymmetry.eta *
          embeddedSplitOctonionHodgeDiracᵀ =
        -(embeddedSplitOctonionHodgeDiracᵀ *
          masterKreinFundamentalSymmetry.eta) := by
    rw [embeddedSplitOctonionHodgeDirac_transpose]
    exact eq_neg_of_add_eq_zero_left masterChirality_anticomm_hodge
  exact (krein_skew_adjoint_iff_hilbert_of_anticomm
    masterKreinFundamentalSymmetry embeddedSplitOctonionHodgeDirac hanticomm).2
      embeddedSplitOctonionHodgeDirac_transpose

/-- 🏆 THEOREM: Square of Master Bounded Transform is $\frac{3}{4} I$. -/
theorem masterBoundedTransform_sq :
    masterBoundedTransform * masterBoundedTransform =
      (3 / 4 : ℝ) • (1 : Mat32) := by
  unfold masterBoundedTransform
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [embeddedSplitOctonionHodgeDirac_sq]
  rw [smul_smul]
  norm_num

/-- The finite normalization is right-invertible with explicit inverse
    `(4 / 3) • F`. -/
theorem masterBoundedTransform_mul_explicitInverse :
    masterBoundedTransform * ((4 / 3 : ℝ) • masterBoundedTransform) =
      (1 : Mat32) := by
  rw [mul_smul_comm, masterBoundedTransform_sq, smul_smul]
  norm_num

/-- The same explicit inverse is also a left inverse. -/
theorem explicitInverse_mul_masterBoundedTransform :
    ((4 / 3 : ℝ) • masterBoundedTransform) * masterBoundedTransform =
      (1 : Mat32) := by
  rw [smul_mul_assoc, masterBoundedTransform_sq, smul_smul]
  norm_num

theorem master_hodge_kernel_trivial
    {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : embeddedSplitOctonionHodgeDirac.mulVec v = 0) :
    v = 0 := by
  have hsq := congrArg
    (fun M : Mat32 => M.mulVec v) embeddedSplitOctonionHodgeDirac_sq
  change (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac).mulVec v =
    ((3 : ℝ) • (1 : Mat32)).mulVec v at hsq
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at hsq
  have hthree : (3 : ℝ) • v = 0 := by
    simpa [Matrix.smul_mulVec, Matrix.one_mulVec] using hsq.symm
  exact (smul_eq_zero.mp hthree).resolve_left (by norm_num)

theorem masterBoundedTransform_kernel_trivial
    {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : masterBoundedTransform.mulVec v = 0) :
    v = 0 := by
  apply master_hodge_kernel_trivial
  simpa [masterBoundedTransform, Matrix.smul_mulVec] using hv

/-- 🏆 THEOREM: Master Bounded Transform is strictly odd with respect to Master Chirality. -/
theorem masterBoundedTransform_anticomm_chirality :
    masterBoundedTransform * MasterChirality +
      MasterChirality * masterBoundedTransform = 0 := by
  unfold masterBoundedTransform
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add]
  have h := masterChirality_anticomm_hodge
  rw [show embeddedSplitOctonionHodgeDirac * MasterChirality +
      MasterChirality * embeddedSplitOctonionHodgeDirac =
      MasterChirality * embeddedSplitOctonionHodgeDirac +
      embeddedSplitOctonionHodgeDirac * MasterChirality by
        rw [add_comm]]
  rw [h, smul_zero]

/-- The finite normalized phase is Krein-skew-adjoint for the concrete
    chirality fundamental symmetry.  This is an algebraic finite-dimensional
    statement; it does not assert an unbounded Kasparov-cycle construction. -/
theorem masterBoundedTransform_krein_skew_adjoint :
    IsKreinSkewAdjoint masterKreinFundamentalSymmetry masterBoundedTransform := by
  have hanticomm :
      masterKreinFundamentalSymmetry.eta * masterBoundedTransformᵀ =
        -(masterBoundedTransformᵀ * masterKreinFundamentalSymmetry.eta) := by
    rw [masterBoundedTransform_transpose]
    exact eq_neg_of_add_eq_zero_right masterBoundedTransform_anticomm_chirality
  exact (krein_skew_adjoint_iff_hilbert_of_anticomm
    masterKreinFundamentalSymmetry masterBoundedTransform hanticomm).2
      masterBoundedTransform_transpose

/-- 🏆 THEOREM: Master Bounded Transform commutes with G₂ spinor derivation action. -/
theorem masterBoundedTransform_comm_g2 (g : G2SpinorRepresentation) :
    g.rho * masterBoundedTransform = masterBoundedTransform * g.rho := by
  unfold masterBoundedTransform
  rw [mul_smul_comm, smul_mul_assoc]
  have h := g.commutes_hodge
  rw [h]

/-- 🏆 THEOREM: Master Bounded Transform satisfies chiral block transition squares. -/
theorem masterBoundedTransform_chiral_transitions :
    masterBoundedTransform * masterChiralProjectorPlus =
        masterChiralProjectorMinus * masterBoundedTransform ∧
      masterBoundedTransform * masterChiralProjectorMinus =
        masterChiralProjectorPlus * masterBoundedTransform := by
  constructor
  · unfold masterBoundedTransform
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    exact masterHodgeDirac_comp_projectorPlus
  · unfold masterBoundedTransform
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    exact masterHodgeDirac_comp_projectorMinus

end InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
