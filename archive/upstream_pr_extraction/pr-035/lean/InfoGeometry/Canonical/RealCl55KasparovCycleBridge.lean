import Mathlib
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
import InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

set_option linter.unusedSimpArgs false

/-!
# Finite Cl(5,5) Clifford Fredholm Datum Bridge

This owner module packages the finite real Clifford action on the 32D spinor
carrier $S_{5,5} \cong \bigwedge^\bullet \mathbb{R}^5$ as a finite Fredholm
datum. It intentionally does not claim the analytic regularity, Hilbert
module, or group-action hypotheses required for a standard Kasparov class:

1. **Spinor Hilbert Carrier**:
   The finite-dimensional Euclidean space $S_{5,5} \cong \mathbb{R}^{32}$.

2. **Real Clifford Action**:
   The 10 Witt creation/annihilation generators $a_i, a_i^\dagger$ ($i \in \{0,\dots,4\}$)
   act on the finite spinor carrier and satisfy the canonical five-mode CAR
   relations.  Generation of the full endomorphism algebra is not claimed in
   this owner:
   $$\{a_i, a_j^\dagger\} = \delta_{ij} I_{32}, \qquad \{a_i, a_j\} = 0, \qquad \{a_i^\dagger, a_j^\dagger\} = 0.$$

3. **Grading / Chirality Operator**:
   $\Gamma = \text{MasterChirality}$ satisfying $\Gamma^2 = I$, $\Gamma^\top = \Gamma$.

4. **Finite odd Fredholm-style matrix datum**:
   $F = \operatorname{masterBoundedTransform} = \frac{1}{2} D_H$, with
   the proved transpose self-adjointness, oddness, and square relations.

5. **Finite-Dimensional Compactness & Fredholm Relations**:
   In finite dimensions $\dim S_{5,5} = 32$, every linear endomorphism is bounded and compact.
   Thus the corresponding finite-dimensional endomorphisms are compact.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55KasparovCycleBridge

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

/-! The Clifford action is part of the datum, rather than being left implicit
in the surrounding namespace.  The profile below records exactly the finite
five-mode CAR relations used by the master spinor construction. -/

structure CAR5Profile where
  creation : Fin 5 → Mat32
  annihilation : Fin 5 → Mat32
  creation_sq : ∀ i, creation i * creation i = 0
  annihilation_sq : ∀ i, annihilation i * annihilation i = 0
  same_site : ∀ i,
    creation i * annihilation i + annihilation i * creation i = 1
  cross_creation : ∀ {i j}, i ≠ j →
    creation i * creation j + creation j * creation i = 0
  cross_annihilation : ∀ {i j}, i ≠ j →
    annihilation i * annihilation j + annihilation j * annihilation i = 0
  cross_creation_annihilation : ∀ {i j}, i ≠ j →
    creation i * annihilation j + annihilation j * creation i = 0
  cross_annihilation_creation : ∀ {i j}, i ≠ j →
    annihilation i * creation j + creation j * annihilation i = 0

def canonicalCAR5Profile : CAR5Profile where
  creation := masterCreation
  annihilation := masterAnnihilation
  creation_sq := masterCreation_sq
  annihilation_sq := masterAnnihilation_sq
  same_site := masterCAR_same_site
  cross_creation := by
    intro i j hij
    exact (masterCAR_cross_site hij).1
  cross_annihilation := by
    intro i j hij
    exact (masterCAR_cross_site hij).2.1
  cross_creation_annihilation := by
    intro i j hij
    exact (masterCAR_cross_site hij).2.2
  cross_annihilation_creation := by
    intro i j hij
    exact InfoGeometry.Canonical.Cl55WittCAR.annihilation_creation_cross_anticommute hij

lemma gamma_chiral_base_transpose : gamma_chiral_baseᵀ = gamma_chiral_base := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]

lemma globalChirality_transpose (k : ℕ) : (globalChirality k)ᵀ = globalChirality k := by
  exact InfoGeometry.Clifford.TowerMatrix.Jn_transpose gamma_chiral_base gamma_chiral_base_transpose k

theorem masterChirality_transpose : MasterChiralityᵀ = MasterChirality := by
  unfold MasterChirality
  exact globalChirality_transpose 5

/-- Structure packaging finite-dimensional real Clifford Fredholm datum on
    $S_{5,5}$; this is not by itself a standard Kasparov module. -/
structure RealCliffordFredholmDatum where
  /-- The finite Clifford/CAR representation on the spinor carrier. -/
  clifford : CAR5Profile
  /-- Chirality grading operator $\Gamma$. -/
  gamma : Mat32
  gamma_sq : gamma * gamma = 1
  gamma_transpose : gammaᵀ = gamma
  /-- Bounded odd self-adjoint operator $F$. -/
  F : Mat32
  F_transpose : Fᵀ = F
  F_odd : F * gamma + gamma * F = 0

/-! Honest finite-datum names.  The older `Kasparov` names below remain as
compatibility API for existing consumers, but these aliases make clear that
no coefficient-algebra representation or standard Kasparov cycle is packaged
here. -/

abbrev RealCliffordFiniteFredholmDatum := RealCliffordFredholmDatum

/-- The canonical master real Clifford Kasparov Fredholm module on $S_{5,5}$. -/
def canonicalMasterRealCliffordFredholmDatum : RealCliffordFredholmDatum where
  clifford := canonicalCAR5Profile
  gamma := MasterChirality
  gamma_sq := masterChirality_sq
  gamma_transpose := masterChirality_transpose
  F := masterBoundedTransform
  F_transpose := masterBoundedTransform_transpose
  F_odd := masterBoundedTransform_anticomm_chirality

abbrev canonicalMasterRealCliffordFiniteFredholmDatum :
    RealCliffordFiniteFredholmDatum := canonicalMasterRealCliffordFredholmDatum

theorem canonicalMasterFredholm_F_transpose :
    canonicalMasterRealCliffordFiniteFredholmDatum.Fᵀ =
      canonicalMasterRealCliffordFiniteFredholmDatum.F := by
  exact canonicalMasterRealCliffordFiniteFredholmDatum.F_transpose

theorem canonicalMasterKasparov_F_transpose :
    canonicalMasterRealCliffordFredholmDatum.Fᵀ =
      canonicalMasterRealCliffordFredholmDatum.F := by
  exact canonicalMasterRealCliffordFredholmDatum.F_transpose

/-- 🏆 THEOREM: The canonical real Clifford Kasparov module satisfies $F^2 - I = -\frac{1}{4} I$. -/
theorem canonicalMasterKasparov_defect_scalar :
    canonicalMasterRealCliffordFredholmDatum.F * canonicalMasterRealCliffordFredholmDatum.F - 1 =
      (-1 / 4 : ℝ) • (1 : Mat32) := by
  dsimp [canonicalMasterRealCliffordFredholmDatum]
  rw [masterBoundedTransform_sq]
  rw [show (3 / 4 : ℝ) • (1 : Mat32) - 1 = (3 / 4 : ℝ) • (1 : Mat32) - (1 : ℝ) • (1 : Mat32) by simp]
  rw [← sub_smul]
  norm_num

theorem canonicalMasterFredholm_defect_scalar :
    canonicalMasterRealCliffordFiniteFredholmDatum.F *
          canonicalMasterRealCliffordFiniteFredholmDatum.F - 1 =
      (-1 / 4 : ℝ) • (1 : Mat32) := by
  exact canonicalMasterKasparov_defect_scalar

/-- The native representative of the finite Fredholm operator is compact.

This is only the finite-dimensional compactness component.  It does not supply
the Hilbert-module, regularity, or equivariant hypotheses of a standard
Kasparov cycle.
-/
theorem canonicalMasterKasparov_native_F_compact :
    IsCompactOperator
      (nativeContinuous canonicalMasterRealCliffordFredholmDatum.F :
        NativeSpinorCarrier → NativeSpinorCarrier) := by
  exact nativeContinuous_is_compact_operator
    canonicalMasterRealCliffordFredholmDatum.F

theorem canonicalMasterFredholm_native_defect_compact :
    IsCompactOperator
      (nativeContinuous
        (canonicalMasterRealCliffordFiniteFredholmDatum.F *
          canonicalMasterRealCliffordFiniteFredholmDatum.F - 1) :
          NativeSpinorCarrier → NativeSpinorCarrier) := by
  exact nativeContinuous_is_compact_operator _

/-- 🏆 THEOREM: Chirality eigenspace decomposition for the Kasparov cycle. -/
theorem canonicalMasterKasparov_chiral_split :
    masterChiralProjectorPlus + masterChiralProjectorMinus = 1 ∧
    masterChiralProjectorPlus * masterChiralProjectorMinus = 0 ∧
    canonicalMasterRealCliffordFredholmDatum.F * masterChiralProjectorPlus =
      masterChiralProjectorMinus * canonicalMasterRealCliffordFredholmDatum.F := by
  refine ⟨masterChiralProjectors_sum,
          masterChiralProjectors_orthogonal.1,
          masterBoundedTransform_chiral_transitions.1⟩

theorem canonicalMasterFredholm_chiral_split :
    masterChiralProjectorPlus + masterChiralProjectorMinus = 1 ∧
    masterChiralProjectorPlus * masterChiralProjectorMinus = 0 ∧
    canonicalMasterRealCliffordFiniteFredholmDatum.F * masterChiralProjectorPlus =
      masterChiralProjectorMinus * canonicalMasterRealCliffordFiniteFredholmDatum.F := by
  exact canonicalMasterKasparov_chiral_split

end InfoGeometry.Canonical.RealCl55KasparovCycleBridge
