import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KK.RealCl55KasparovCycleBridge
import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge

/-!
# Group-action covariance contract for the finite `Cl(5,5)` carrier

This module records the exact group-action covariance datum on the 32D spinor carrier $S_{5,5}$:
a genuine group homomorphism into $\mathrm{GL}_{32}(\mathbb{R})$ together with covariance
of the master chirality grading $\Gamma$ and the normalized master Hodge-Dirac operator $F$.

This module makes clear the theoretical distinction between:
- Infinitesimal $\mathfrak{g}_{2(2)}$ Lie algebra equivariance (Layer III, fully proved in-repo).
- Integrated group-action covariance for a Lie group $G$ (Layer IV, formulated as a covariance contract datum).
-/

noncomputable section

namespace InfoGeometry.KK.G2IntegratedKasparovEquivarianceBridge

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.KK.RealCl55KasparovCycleBridge

abbrev Mat32 := InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.Mat32
abbrev GL32 := Matrix.GeneralLinearGroup (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℝ

def conjugate (u : GL32) (T : Mat32) : Mat32 :=
  (u : Mat32) * T * (↑(u⁻¹) : Mat32)

lemma coe_mul_inv (u : GL32) :
    (u : Mat32) * (↑(u⁻¹) : Mat32) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul]
  simp

lemma coe_inv_mul (u : GL32) :
    (↑(u⁻¹) : Mat32) * (u : Mat32) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul]
  simp

@[simp] theorem conjugate_one (u : GL32) :
    conjugate u (1 : Mat32) = 1 := by
  unfold conjugate
  simp only [mul_one]
  exact coe_mul_inv u

theorem conjugate_add (u : GL32) (S T : Mat32) :
    conjugate u (S + T) = conjugate u S + conjugate u T := by
  unfold conjugate
  simp only [add_mul, mul_add]

theorem conjugate_sub (u : GL32) (S T : Mat32) :
    conjugate u (S - T) = conjugate u S - conjugate u T := by
  unfold conjugate
  simp only [sub_mul, mul_sub]

theorem conjugate_mul (u : GL32) (S T : Mat32) :
    conjugate u (S * T) = conjugate u S * conjugate u T := by
  unfold conjugate
  calc
    (u : Mat32) * (S * T) * (↑(u⁻¹) : Mat32) =
        (u : Mat32) * S * ((↑(u⁻¹) : Mat32) * (u : Mat32)) *
          T * (↑(u⁻¹) : Mat32) := by
            rw [coe_inv_mul u]
            simp only [mul_one, mul_assoc]
    _ = ((u : Mat32) * S * (↑(u⁻¹) : Mat32)) *
          ((u : Mat32) * T * (↑(u⁻¹) : Mat32)) := by
            calc
              (u : Mat32) * S * ((↑(u⁻¹) : Mat32) * (u : Mat32)) *
                  T * (↑(u⁻¹) : Mat32) =
                  (u : Mat32) * S * (1 : Mat32) * T *
                    (↑(u⁻¹) : Mat32) := by rw [coe_inv_mul u]
              _ = ((u : Mat32) * S * (↑(u⁻¹) : Mat32)) *
                  ((u : Mat32) * T * (↑(u⁻¹) : Mat32)) := by
                    calc
                      (u : Mat32) * S * (1 : Mat32) * T *
                          (↑(u⁻¹) : Mat32) =
                          (u : Mat32) * S *
                            ((↑(u⁻¹) : Mat32) * (u : Mat32)) * T *
                              (↑(u⁻¹) : Mat32) := by
                                rw [coe_inv_mul u]
                      _ = ((u : Mat32) * S * (↑(u⁻¹) : Mat32)) *
                          ((u : Mat32) * T * (↑(u⁻¹) : Mat32)) := by
                            simp only [Matrix.mul_assoc]

theorem conjugate_smul (u : GL32) (c : ℝ) (T : Mat32) :
    conjugate u (c • T) = c • conjugate u T := by
  unfold conjugate
  simp only [smul_mul_assoc, mul_smul_comm]

theorem conjugate_pow (u : GL32) (T : Mat32) (n : ℕ) :
    conjugate u (T ^ n) = (conjugate u T) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, conjugate_mul, ih, pow_succ]

theorem conjugate_commutator (u : GL32) (S T : Mat32) :
    conjugate u (S * T - T * S) =
      conjugate u S * conjugate u T - conjugate u T * conjugate u S := by
  rw [conjugate_sub, conjugate_mul, conjugate_mul]

theorem conjugate_anticommutator (u : GL32) (S T : Mat32) :
    conjugate u (S * T + T * S) =
      conjugate u S * conjugate u T + conjugate u T * conjugate u S := by
  rw [conjugate_add, conjugate_mul, conjugate_mul]

lemma conjugate_eq_of_commute (u : GL32) (T : Mat32)
    (hcomm : (u : Mat32) * T = T * (u : Mat32)) :
    conjugate u T = T := by
  unfold conjugate
  calc
    (u : Mat32) * T * (↑(u⁻¹) : Mat32) =
        T * (u : Mat32) * (↑(u⁻¹) : Mat32) := by rw [hcomm]
    _ = T * ((u : Mat32) * (↑(u⁻¹) : Mat32)) := by rw [mul_assoc]
    _ = T := by rw [coe_mul_inv, mul_one]

/--
Integrated group action datum on the 32D spinor carrier $S_{5,5}$.
Packages a group homomorphism $U : G \to \mathrm{GL}_{32}(\mathbb{R})$ that commutes
with the master chirality $\Gamma$ and the Hodge-Dirac operator $D_H$.
-/
structure IntegratedCl55ActionDatum (G : Type*) [Group G] where
  U : G →* GL32
  preserves_chirality : ∀ g, (U g : Mat32) * MasterChirality =
    MasterChirality * (U g : Mat32)
  preserves_hodge : ∀ g, (U g : Mat32) * embeddedSplitOctonionHodgeDirac =
    embeddedSplitOctonionHodgeDirac * (U g : Mat32)

theorem covariance_chirality {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) MasterChirality = MasterChirality := by
  exact conjugate_eq_of_commute (X.U g) MasterChirality (X.preserves_chirality g)

theorem covariance_hodge {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac := by
  exact conjugate_eq_of_commute (X.U g) embeddedSplitOctonionHodgeDirac
    (X.preserves_hodge g)

theorem covariance_normalized_hodge {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) normalizedMasterHodgeDirac = normalizedMasterHodgeDirac := by
  unfold normalizedMasterHodgeDirac
  rw [conjugate_smul, covariance_hodge X g]

theorem covariance_chiral_projector_plus {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) masterChiralProjectorPlus = masterChiralProjectorPlus := by
  apply conjugate_eq_of_commute
  unfold masterChiralProjectorPlus
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [X.preserves_chirality g]

theorem covariance_chiral_projector_minus {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) masterChiralProjectorMinus = masterChiralProjectorMinus := by
  apply conjugate_eq_of_commute
  unfold masterChiralProjectorMinus
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, sub_mul, mul_one, one_mul]
  rw [X.preserves_chirality g]

theorem covariance_normalized_hodge_sq {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) (normalizedMasterHodgeDirac * normalizedMasterHodgeDirac) =
      normalizedMasterHodgeDirac * normalizedMasterHodgeDirac := by
  rw [conjugate_mul, covariance_normalized_hodge X g]

theorem covariance_normalized_hodge_pow {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) (n : ℕ) :
    conjugate (X.U g) (normalizedMasterHodgeDirac ^ n) =
      normalizedMasterHodgeDirac ^ n := by
  rw [conjugate_pow, covariance_normalized_hodge X g]

theorem covariance_normalized_hodge_defect {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) (g : G) :
    conjugate (X.U g) (normalizedMasterHodgeDirac * normalizedMasterHodgeDirac - 1) =
      normalizedMasterHodgeDirac * normalizedMasterHodgeDirac - 1 := by
  rw [conjugate_sub, conjugate_one, covariance_normalized_hodge_sq X g]

/--
An integrated group-equivariant Kasparov cycle certificate on the 32D spinor carrier $S_{5,5}$.
Records the group action covariance together with the involution and anti-commutation axioms.
-/
structure IntegratedGroupKasparovDatum (G : Type*) [Group G] where
  action : IntegratedCl55ActionDatum G
  gamma : Mat32
  F : Mat32
  gamma_sq : gamma * gamma = 1
  F_sq : F * F = 1
  anticomm : F * gamma + gamma * F = 0
  cov_gamma : ∀ g : G, conjugate (action.U g) gamma = gamma
  cov_F : ∀ g : G, conjugate (action.U g) F = F

/-- Canonical realization of the integrated group Kasparov datum given an action certificate. -/
def canonicalIntegratedGroupKasparovDatum {G : Type*} [Group G]
    (X : IntegratedCl55ActionDatum G) : IntegratedGroupKasparovDatum G where
  action := X
  gamma := MasterChirality
  F := normalizedMasterHodgeDirac
  gamma_sq := masterChirality_sq
  F_sq := normalizedMasterHodgeDirac_sq
  anticomm := normalizedMasterHodgeDirac_anticomm_chirality
  cov_gamma g := covariance_chirality X g
  cov_F g := covariance_normalized_hodge X g

end InfoGeometry.KK.G2IntegratedKasparovEquivarianceBridge
