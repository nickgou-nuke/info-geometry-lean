import InfoGeometry.Canonical.BiQuaternionKahlerFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite
import InfoGeometry.Canonical.BiQuaternionKahlerSymplecticNoetherBridge
import InfoGeometry.Canonical.HodgeStar4DFinite
import InfoGeometry.Potential.Thermo
import InfoGeometry.Section26

/-!
# Section 27: finite bi-quaternion-Kähler bridge

This capstone only packages existing finite owners.  It does not promote the
corresponding smooth, continuum, or representation-theoretic conjectures to
theorems.
-/

noncomputable section

namespace Section27

open InfoGeometry.Canonical.BiQuaternionKahlerFinite
open InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite
open InfoGeometry.Canonical.BiQuaternionKahlerSymplecticNoetherBridge

theorem biQuaternion_complexStructure_packet :
    I4c * I4c = -1 ∧
    J4c * J4c = -1 ∧
    K4c * K4c = -1 ∧
    I4c * J4c = K4c ∧
    J4c * I4c = -K4c :=
  ⟨I4c_sq, J4c_sq, K4c_sq, I4c_mul_J4c, J4c_mul_I4c⟩

theorem biQuaternion_symplectic_poisson_packet :
    (∀ x y : R4, symplecticI x y = -symplecticI y x) ∧
    (∀ dF dG : R4, finitePoissonBracket dF dG = -finitePoissonBracket dG dF) :=
  ⟨symplecticI_skew, finitePoissonBracket_skew⟩

theorem biQuaternion_legendre_packet :
    (∀ V : R4 → ℝ, ∀ q v : R4,
      legendreReadout V q v = hamiltonian V q (conjugateMomentum v)) ∧
    (∀ V : R4 → ℝ, ∀ q p : R4, 0 ≤ V q → 0 ≤ hamiltonian V q p) :=
  ⟨legendreReadout_eq_hamiltonian, hamiltonian_nonneg_of_potential_nonneg⟩

theorem biQuaternion_noether_packet :
    (∀ q p : R4, finiteNoetherReadback (fun x : R4 => x) q p = 0) ∧
    (∀ q p : R4,
      hamiltonian kinetic (I4c.mulVec q) (I4c.mulVec p) = hamiltonian kinetic q p) :=
  ⟨finiteNoetherReadback_radial_zero, radialQuadraticHamiltonian_I4c_invariant⟩

theorem hodge4D_packet :
    (∀ F : InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC,
      InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar
        (InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar F) = -F) ∧
    (∀ F : InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC,
      (fun i =>
        InfoGeometry.Canonical.HodgeStar4DFinite.selfDualPart F i +
          InfoGeometry.Canonical.HodgeStar4DFinite.antiSelfDualPart F i) = F) ∧
    (∀ F : InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC,
      InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar
          (InfoGeometry.Canonical.HodgeStar4DFinite.selfDualPart F) =
        fun i => Complex.I *
          InfoGeometry.Canonical.HodgeStar4DFinite.selfDualPart F i) ∧
    (∀ F : InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC,
      InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar
          (InfoGeometry.Canonical.HodgeStar4DFinite.antiSelfDualPart F) =
        fun i => -Complex.I *
          InfoGeometry.Canonical.HodgeStar4DFinite.antiSelfDualPart F i) :=
  ⟨InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar_sq,
    InfoGeometry.Canonical.HodgeStar4DFinite.self_plus_anti,
    InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar_selfDualPart,
    InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar_antiSelfDualPart⟩

theorem massieu_legendre_packet (M : InfoGeometry.LogPotential.LegendreModel) :
    (∀ θ η : ℝ, 0 ≤ M.fenchelGap θ η) ∧
    (∀ θ : ℝ, M.fenchelGap θ (M.dualCoord θ) = 0) ∧
    (∀ θ : ℝ, M.entropy θ = M.φ (M.dualCoord θ)) ∧
    (∀ β θ η : ℝ, 0 ≤ β → 0 ≤ M.temperatureRegularizedHamiltonian β θ η) :=
  ⟨M.fenchelGap_nonneg, M.fenchelGap_eq_zero_at_contact,
    M.entropy_eq_dual_at_contact, M.temperatureRegularizedHamiltonian_nonneg⟩

theorem section27_capstone (M : InfoGeometry.LogPotential.LegendreModel) :
    (I4c * I4c = -1 ∧ J4c * J4c = -1 ∧ K4c * K4c = -1 ∧
      I4c * J4c = K4c ∧ J4c * I4c = -K4c) ∧
    (∀ x y : R4, symplecticI x y = -symplecticI y x) ∧
    (∀ V : R4 → ℝ, ∀ q v : R4,
      legendreReadout V q v = hamiltonian V q (conjugateMomentum v)) ∧
    (∀ q p : R4, finiteNoetherReadback (fun x : R4 => x) q p = 0) ∧
    (∀ F : InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC,
      InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar
        (InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar F) = -F) ∧
    (∀ θ : ℝ, M.fenchelGap θ (M.dualCoord θ) = 0) := by
  exact ⟨biQuaternion_complexStructure_packet, symplecticI_skew,
    legendreReadout_eq_hamiltonian, finiteNoetherReadback_radial_zero,
    InfoGeometry.Canonical.HodgeStar4DFinite.hodgeStar_sq,
    (massieu_legendre_packet M).2.1⟩

end Section27
