/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55AllModeMassCoercivity
import InfoGeometry.Canonical.Cl55InfinityChiralCharge
import InfoGeometry.Clifford.Cl55WittCalibratedColimit
import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.OperatorAlgebra.Cl55CARBdGInteractionBridge
import InfoGeometry.Canonical.CARCCRColimitSupercarrier

/-!
# Chiral commutator of the native five-mode mass

The five-mode Majorana interaction is not invariant under the established
chiral charge.  Its commutator is the explicit operator supported on modes
zero and one.  The CAR relations show this defect is nonzero, so the mass
breaks this chiral symmetry on the native finite Clifford carrier.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55MassChiralSymmetryBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55AllModeMassCoercivity
open InfoGeometry.Canonical.Cl55InfinityChiralCharge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Physics
open InfoGeometry.Clifford.Cl55WittCalibratedColimit
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Canonical.CliffordCARGeneratorTopological
open InfoGeometry.OperatorAlgebra.Cl55CARBdGInteractionBridge
open InfoGeometry.Canonical.CARCCRColimitSupercarrier

/-- The chiral component of the five-mode Majorana mass commutator. -/
def nativeFiveModeChiralDefect : Cl55 :=
  (creation55 0 - annihilation55 0) - (creation55 1 - annihilation55 1)

/-- The calibrated colimit image of the native mass is the sum of the actual
five finite-stage CAR creation and annihilation modes. -/
theorem cl55WittColimit_nativeFiveModeMajorana_eq_finite_sum :
    cl55WittColimit nativeFiveModeMajorana =
      ∑ i : Fin 5,
        (algebraicCreationElement 5 i + algebraicAnnihilationElement 5 i) := by
  unfold nativeFiveModeMajorana
  simp only [map_sum, map_add, cl55WittColimit_creation55,
    cl55WittColimit_annihilation55]

private theorem chiralCharge55_commutator_mode (i : Fin 5) :
    chiralCharge55 * (creation55 i + annihilation55 i) -
        (creation55 i + annihilation55 i) * chiralCharge55 =
      (chiralModeWeight55 i : ℝ) • creation55 i +
        ((-chiralModeWeight55 i : ℤ) : ℝ) • annihilation55 i := by
  have hc := creation55_has_chiralCharge_grade i
  have ha := annihilation55_has_chiralCharge_grade i
  unfold HasOperatorGrade at hc ha
  calc
    _ = (chiralCharge55 * creation55 i - creation55 i * chiralCharge55) +
        (chiralCharge55 * annihilation55 i - annihilation55 i * chiralCharge55) := by
      noncomm_ring
    _ = _ := by rw [hc, ha]

theorem chiralCharge55_commutator_nativeFiveModeMajorana :
    chiralCharge55 * nativeFiveModeMajorana -
        nativeFiveModeMajorana * chiralCharge55 =
      nativeFiveModeChiralDefect := by
  unfold nativeFiveModeMajorana
  calc
    _ = ∑ i : Fin 5,
        (chiralCharge55 * (creation55 i + annihilation55 i) -
          (creation55 i + annihilation55 i) * chiralCharge55) := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    _ = ∑ i : Fin 5,
        ((chiralModeWeight55 i : ℝ) • creation55 i +
          ((-chiralModeWeight55 i : ℤ) : ℝ) • annihilation55 i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact chiralCharge55_commutator_mode i
    _ = nativeFiveModeChiralDefect := by
      simp [nativeFiveModeChiralDefect, chiralModeWeight55,
        Fin.sum_univ_succ]; abel

theorem nativeFiveModeChiralDefect_anticomm_annihilation_zero :
    nativeFiveModeChiralDefect * annihilation55 0 +
        annihilation55 0 * nativeFiveModeChiralDefect = 1 := by
  unfold nativeFiveModeChiralDefect
  have h00 := annihilation55_creation55_anticommutator (0 : Fin 5)
  have h01 := annihilation55_creation55_anticommutator_eq
    (0 : Fin 5) (1 : Fin 5)
  have haa := annihilation55_anticommutator (0 : Fin 5) (1 : Fin 5)
  simp only [Fin.zero_ne_one, ite_false] at h01
  calc
    _ = (annihilation55 0 * creation55 0 +
        creation55 0 * annihilation55 0) -
        (annihilation55 0 * annihilation55 0 +
          annihilation55 0 * annihilation55 0) -
        (annihilation55 0 * creation55 1 +
          creation55 1 * annihilation55 0) +
        (annihilation55 0 * annihilation55 1 +
          annihilation55 1 * annihilation55 0) := by noncomm_ring
    _ = 1 := by
      rw [h00, annihilation55_sq, h01, haa]
      simp

theorem nativeFiveModeChiralDefect_ne_zero :
    nativeFiveModeChiralDefect ≠ 0 := by
  intro h
  have hone := congrArg
    (fun x : Cl55 => x * annihilation55 0 + annihilation55 0 * x) h
  rw [nativeFiveModeChiralDefect_anticomm_annihilation_zero] at hone
  have hzero : (1 : Cl55) = 0 := by
    simpa only [zero_mul, mul_zero, add_zero] using hone
  exact one_ne_zero hzero

theorem chiralCharge55_does_not_commute_with_nativeFiveModeMajorana :
    chiralCharge55 * nativeFiveModeMajorana -
        nativeFiveModeMajorana * chiralCharge55 ≠ 0 := by
  rw [chiralCharge55_commutator_nativeFiveModeMajorana]
  exact nativeFiveModeChiralDefect_ne_zero

/-- The nonzero chiral commutator enters the off-diagonal block of the
massive BdG square, where Andreev reflection negates it and the particle-hole
pair cancels it exactly. The underlying Cl(5,5) commutator remains nonzero. -/
theorem nativeFiveMode_chiral_bdg_anomaly_andreev_cancellation :
    massiveBdGCommutatorAnomaly chiralCharge55 nativeFiveModeMajorana ≠ 0 ∧
    massiveBdGCommutatorAnomaly chiralCharge55 nativeFiveModeMajorana +
      andreevSwap *
        massiveBdGCommutatorAnomaly chiralCharge55 nativeFiveModeMajorana *
        andreevSwap = 0 ∧
    massiveBdGHamiltonian chiralCharge55 nativeFiveModeMajorana *
        massiveBdGHamiltonian chiralCharge55 nativeFiveModeMajorana +
      andreevSwap *
        (massiveBdGHamiltonian chiralCharge55 nativeFiveModeMajorana *
          massiveBdGHamiltonian chiralCharge55 nativeFiveModeMajorana) *
        andreevSwap =
      !![chiralCharge55 * chiralCharge55 +
          nativeFiveModeMajorana * nativeFiveModeMajorana +
          (nativeFiveModeMajorana * nativeFiveModeMajorana +
            chiralCharge55 * chiralCharge55), 0;
         0, nativeFiveModeMajorana * nativeFiveModeMajorana +
          chiralCharge55 * chiralCharge55 +
          (chiralCharge55 * chiralCharge55 +
            nativeFiveModeMajorana * nativeFiveModeMajorana)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hcomm :=
      (massiveBdGCommutatorAnomaly_eq_zero_iff_commute
        chiralCharge55 nativeFiveModeMajorana).mp h
    exact chiralCharge55_does_not_commute_with_nativeFiveModeMajorana
      (sub_eq_zero.mpr hcomm)
  · rw [andreev_reflect_mass_commutator_anomaly]
    exact add_neg_cancel
      (massiveBdGCommutatorAnomaly chiralCharge55 nativeFiveModeMajorana)
  · exact massiveBdGHamiltonian_andreev_anomaly_cancellation
      chiralCharge55 nativeFiveModeMajorana

/-- The same nonzero chiral defect and its particle–hole cancellation hold
after applying the repository's faithful Witt-calibrated map into the actual
algebraic matrix colimit. No completion or analytic limit is asserted. -/
theorem chiral_mass_bdg_anomaly_survives_witt_colimit :
    cl55WittColimit chiralCharge55 *
        cl55WittColimit nativeFiveModeMajorana -
      cl55WittColimit nativeFiveModeMajorana *
        cl55WittColimit chiralCharge55 =
      cl55WittColimit nativeFiveModeChiralDefect ∧
    cl55WittColimit chiralCharge55 *
        cl55WittColimit nativeFiveModeMajorana -
      cl55WittColimit nativeFiveModeMajorana *
        cl55WittColimit chiralCharge55 ≠ 0 ∧
    massiveBdGCommutatorAnomaly
        (cl55WittColimit chiralCharge55)
        (cl55WittColimit nativeFiveModeMajorana) ≠ 0 ∧
    massiveBdGCommutatorAnomaly
        (cl55WittColimit chiralCharge55)
        (cl55WittColimit nativeFiveModeMajorana) +
      andreevSwap *
        massiveBdGCommutatorAnomaly
          (cl55WittColimit chiralCharge55)
          (cl55WittColimit nativeFiveModeMajorana) *
        andreevSwap = 0 ∧
    massiveBdGHamiltonian
        (cl55WittColimit chiralCharge55)
        (cl55WittColimit nativeFiveModeMajorana) *
        massiveBdGHamiltonian
          (cl55WittColimit chiralCharge55)
          (cl55WittColimit nativeFiveModeMajorana) +
      andreevSwap *
        (massiveBdGHamiltonian
          (cl55WittColimit chiralCharge55)
          (cl55WittColimit nativeFiveModeMajorana) *
          massiveBdGHamiltonian
            (cl55WittColimit chiralCharge55)
            (cl55WittColimit nativeFiveModeMajorana)) *
        andreevSwap =
      !![(cl55WittColimit chiralCharge55) *
            (cl55WittColimit chiralCharge55) +
          (cl55WittColimit nativeFiveModeMajorana) *
            (cl55WittColimit nativeFiveModeMajorana) +
          ((cl55WittColimit nativeFiveModeMajorana) *
              (cl55WittColimit nativeFiveModeMajorana) +
            (cl55WittColimit chiralCharge55) *
              (cl55WittColimit chiralCharge55)), 0;
         0, (cl55WittColimit nativeFiveModeMajorana) *
              (cl55WittColimit nativeFiveModeMajorana) +
            (cl55WittColimit chiralCharge55) *
              (cl55WittColimit chiralCharge55) +
            ((cl55WittColimit chiralCharge55) *
                (cl55WittColimit chiralCharge55) +
              (cl55WittColimit nativeFiveModeMajorana) *
                (cl55WittColimit nativeFiveModeMajorana))] := by
  have hcomm := congrArg cl55WittColimit
    chiralCharge55_commutator_nativeFiveModeMajorana
  have hcommLim :
      cl55WittColimit chiralCharge55 *
          cl55WittColimit nativeFiveModeMajorana -
        cl55WittColimit nativeFiveModeMajorana *
          cl55WittColimit chiralCharge55 =
        cl55WittColimit nativeFiveModeChiralDefect := by
    simpa only [map_sub, map_mul] using hcomm
  refine ⟨hcommLim, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hfinite :
        chiralCharge55 * nativeFiveModeMajorana -
          nativeFiveModeMajorana * chiralCharge55 = 0 := by
      apply cl55WittColimit_injective
      simpa only [map_zero, map_sub, map_mul] using hzero
    exact chiralCharge55_does_not_commute_with_nativeFiveModeMajorana hfinite
  · intro hzero
    have hcommute :=
      (massiveBdGCommutatorAnomaly_eq_zero_iff_commute
        (cl55WittColimit chiralCharge55)
        (cl55WittColimit nativeFiveModeMajorana)).mp hzero
    exact (chiralCharge55_does_not_commute_with_nativeFiveModeMajorana)
      (by
        apply cl55WittColimit_injective
        rw [map_sub, map_mul, map_mul, map_zero]
        exact sub_eq_zero.mpr hcommute)
  · rw [andreev_reflect_mass_commutator_anomaly]
    exact add_neg_cancel
      (massiveBdGCommutatorAnomaly
        (cl55WittColimit chiralCharge55)
        (cl55WittColimit nativeFiveModeMajorana))
  · exact massiveBdGHamiltonian_andreev_anomaly_cancellation
      (cl55WittColimit chiralCharge55)
      (cl55WittColimit nativeFiveModeMajorana)

/-- The same mass defect is a nonzero operator on the existing exterior-spinor
ideal representation. Its BdG hole copy cancels the anomaly in the doubled
spinor endomorphism carrier. -/
theorem chiral_mass_bdg_anomaly_survives_exterior_spinor :
    massiveBdGCommutatorAnomaly
        (cl55SpinorRep chiralCharge55)
        (cl55SpinorRep nativeFiveModeMajorana) ≠ 0 ∧
    massiveBdGCommutatorAnomaly
        (cl55SpinorRep chiralCharge55)
        (cl55SpinorRep nativeFiveModeMajorana) +
      andreevSwap *
        massiveBdGCommutatorAnomaly
          (cl55SpinorRep chiralCharge55)
          (cl55SpinorRep nativeFiveModeMajorana) *
        andreevSwap = 0 ∧
    massiveBdGHamiltonian
        (cl55SpinorRep chiralCharge55)
        (cl55SpinorRep nativeFiveModeMajorana) *
        massiveBdGHamiltonian
          (cl55SpinorRep chiralCharge55)
          (cl55SpinorRep nativeFiveModeMajorana) +
      andreevSwap *
        (massiveBdGHamiltonian
          (cl55SpinorRep chiralCharge55)
          (cl55SpinorRep nativeFiveModeMajorana) *
          massiveBdGHamiltonian
            (cl55SpinorRep chiralCharge55)
            (cl55SpinorRep nativeFiveModeMajorana)) *
        andreevSwap =
      !![(cl55SpinorRep chiralCharge55) *
            (cl55SpinorRep chiralCharge55) +
          (cl55SpinorRep nativeFiveModeMajorana) *
            (cl55SpinorRep nativeFiveModeMajorana) +
          ((cl55SpinorRep nativeFiveModeMajorana) *
              (cl55SpinorRep nativeFiveModeMajorana) +
            (cl55SpinorRep chiralCharge55) *
              (cl55SpinorRep chiralCharge55)), 0;
         0, (cl55SpinorRep nativeFiveModeMajorana) *
              (cl55SpinorRep nativeFiveModeMajorana) +
            (cl55SpinorRep chiralCharge55) *
              (cl55SpinorRep chiralCharge55) +
            ((cl55SpinorRep chiralCharge55) *
                (cl55SpinorRep chiralCharge55) +
              (cl55SpinorRep nativeFiveModeMajorana) *
                (cl55SpinorRep nativeFiveModeMajorana))] := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hcommute :=
      (massiveBdGCommutatorAnomaly_eq_zero_iff_commute
        (cl55SpinorRep chiralCharge55)
        (cl55SpinorRep nativeFiveModeMajorana)).mp hzero
    apply chiralCharge55_does_not_commute_with_nativeFiveModeMajorana
    apply cl55SpinorRep_injective
    rw [map_sub, map_mul, map_mul, map_zero]
    exact sub_eq_zero.mpr hcommute
  · rw [andreev_reflect_mass_commutator_anomaly]
    exact add_neg_cancel
      (massiveBdGCommutatorAnomaly
        (cl55SpinorRep chiralCharge55)
        (cl55SpinorRep nativeFiveModeMajorana))
  · exact massiveBdGHamiltonian_andreev_anomaly_cancellation
      (cl55SpinorRep chiralCharge55)
      (cl55SpinorRep nativeFiveModeMajorana)

/-- The native chiral commutator is transported by the actual Cl(5,5) action
on the polynomial–Fock colimit carrier. -/
theorem chiral_mass_commutator_on_CARCCR_colimit :
    cl55ColimitSupercarrierRep chiralCharge55 *
        cl55ColimitSupercarrierRep nativeFiveModeMajorana -
      cl55ColimitSupercarrierRep nativeFiveModeMajorana *
        cl55ColimitSupercarrierRep chiralCharge55 =
      cl55ColimitSupercarrierRep nativeFiveModeChiralDefect := by
  have h := congrArg cl55ColimitSupercarrierRep
    chiralCharge55_commutator_nativeFiveModeMajorana
  simpa only [map_sub, map_mul] using h

/-- CAR detects the chiral defect on the polynomial–Fock colimit: its
anticommutator with the represented zero-mode annihilator is the identity. -/
theorem chiral_defect_CAR_readout_on_colimit :
    cl55ColimitSupercarrierRep nativeFiveModeChiralDefect *
        cl55ColimitSupercarrierRep (annihilation55 0) +
      cl55ColimitSupercarrierRep (annihilation55 0) *
        cl55ColimitSupercarrierRep nativeFiveModeChiralDefect =
      1 := by
  have h := congrArg cl55ColimitSupercarrierRep
    nativeFiveModeChiralDefect_anticomm_annihilation_zero
  simpa only [map_add, map_mul, map_one] using h

/-- The transported chiral defect and hence the represented mass commutator
remain nonzero on the actual CCR–CAR colimit carrier. -/
theorem chiral_mass_commutator_nonzero_on_CARCCR_colimit :
    cl55ColimitSupercarrierRep chiralCharge55 *
        cl55ColimitSupercarrierRep nativeFiveModeMajorana -
      cl55ColimitSupercarrierRep nativeFiveModeMajorana *
        cl55ColimitSupercarrierRep chiralCharge55 ≠ 0 := by
  rw [chiral_mass_commutator_on_CARCCR_colimit]
  letI : Nontrivial Carrier := commonCarrier_nontrivial
  intro hzero
  have hone := congrArg
    (fun x : Module.End ℝ Carrier =>
      x * cl55ColimitSupercarrierRep (annihilation55 0) +
        cl55ColimitSupercarrierRep (annihilation55 0) * x) hzero
  rw [chiral_defect_CAR_readout_on_colimit] at hone
  exact one_ne_zero hone

/-- The mass anomaly is nonzero on the shared CCR–CAR colimit, while its
Andreev-reflected hole contribution cancels it in the doubled BdG square. -/
theorem chiral_mass_BdG_andreev_cancellation_on_CARCCR_colimit :
    massiveBdGCommutatorAnomaly
        (cl55ColimitSupercarrierRep chiralCharge55)
        (cl55ColimitSupercarrierRep nativeFiveModeMajorana) ≠ 0 ∧
    massiveBdGCommutatorAnomaly
        (cl55ColimitSupercarrierRep chiralCharge55)
        (cl55ColimitSupercarrierRep nativeFiveModeMajorana) +
      andreevSwap *
        massiveBdGCommutatorAnomaly
          (cl55ColimitSupercarrierRep chiralCharge55)
          (cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
        andreevSwap = 0 ∧
    massiveBdGHamiltonian
        (cl55ColimitSupercarrierRep chiralCharge55)
        (cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
        massiveBdGHamiltonian
          (cl55ColimitSupercarrierRep chiralCharge55)
          (cl55ColimitSupercarrierRep nativeFiveModeMajorana) +
      andreevSwap *
        (massiveBdGHamiltonian
          (cl55ColimitSupercarrierRep chiralCharge55)
          (cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
          massiveBdGHamiltonian
            (cl55ColimitSupercarrierRep chiralCharge55)
            (cl55ColimitSupercarrierRep nativeFiveModeMajorana)) *
        andreevSwap =
      !![(cl55ColimitSupercarrierRep chiralCharge55) *
            (cl55ColimitSupercarrierRep chiralCharge55) +
          (cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
            (cl55ColimitSupercarrierRep nativeFiveModeMajorana) +
          ((cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
              (cl55ColimitSupercarrierRep nativeFiveModeMajorana) +
            (cl55ColimitSupercarrierRep chiralCharge55) *
              (cl55ColimitSupercarrierRep chiralCharge55)), 0;
         0, (cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
              (cl55ColimitSupercarrierRep nativeFiveModeMajorana) +
            (cl55ColimitSupercarrierRep chiralCharge55) *
              (cl55ColimitSupercarrierRep chiralCharge55) +
            ((cl55ColimitSupercarrierRep chiralCharge55) *
                (cl55ColimitSupercarrierRep chiralCharge55) +
              (cl55ColimitSupercarrierRep nativeFiveModeMajorana) *
                (cl55ColimitSupercarrierRep nativeFiveModeMajorana))] := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hcommute :=
      (massiveBdGCommutatorAnomaly_eq_zero_iff_commute
        (cl55ColimitSupercarrierRep chiralCharge55)
        (cl55ColimitSupercarrierRep nativeFiveModeMajorana)).mp hzero
    exact chiral_mass_commutator_nonzero_on_CARCCR_colimit
      (sub_eq_zero.mpr hcommute)
  · rw [andreev_reflect_mass_commutator_anomaly]
    exact add_neg_cancel
      (massiveBdGCommutatorAnomaly
        (cl55ColimitSupercarrierRep chiralCharge55)
        (cl55ColimitSupercarrierRep nativeFiveModeMajorana))
  · exact massiveBdGHamiltonian_andreev_anomaly_cancellation
      (cl55ColimitSupercarrierRep chiralCharge55)
      (cl55ColimitSupercarrierRep nativeFiveModeMajorana)

end InfoGeometry.Canonical.Cl55MassChiralSymmetryBridge
