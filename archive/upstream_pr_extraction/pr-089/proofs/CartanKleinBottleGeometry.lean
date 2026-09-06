import proofs.MobiusCantorTKKClosure
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import proofs.Clifford55AnomalyOSP
import proofs.MajoranaPrimonSpectralBridge

noncomputable section

namespace CartanKleinBottleGeometry

open MobiusCantorTKKClosure
open ProjectiveAffineConformalClosure55
open MajoranaPrimonSpectralBridge
open Clifford55AnomalyOSP

structure SpectralInvolution (V : Type*) where
  theta : V → V
  involutive : ∀ v, theta (theta v) = v
  fixedLocus : Set V

def cptSpectralInvolution : SpectralInvolution ℂ := {
  theta := cptSpectralMap
  involutive := λ s => by dsimp [cptSpectralMap]; simp
  fixedLocus := {s | s.re = 1/2}
}

theorem cpt_is_involution (s : ℂ) :
    cptSpectralMap (cptSpectralMap s) = s :=
  cptSpectralInvolution.involutive s

theorem cpt_fixed_locus_is_critical_line (s : ℂ) :
    cptSpectralMap s = s ↔ s.re = 1/2 :=
  cpt_fixed_point_iff_critical_line s

theorem cpt_spectral_map_sq (s : ℂ) :
    cptSpectralMap (cptSpectralMap s) = s :=
  cptSpectralInvolution.involutive s

theorem critical_line_is_cpt_fixed_line (s : ℂ) :
    cptSpectralMap s = s ↔ s.re = 1/2 :=
  cpt_fixed_point_iff_critical_line s

theorem anomalyIndex_55_zero_imported :
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 :=
  Clifford55AnomalyOSP.anomalyIndex_55_zero

theorem mobius_v4_identities (z : ℂ) :
    mobiusJ (mobiusJ z) = z ∧
    mobiusGamma (mobiusGamma z) = z ∧
    mobiusJ (mobiusGamma z) = mobiusGamma (mobiusJ z) :=
  ⟨mobiusJ_involutive z, mobiusGamma_involutive z, mobiusJ_gamma_commute z⟩

theorem cartan_symmetric_space_finite_check :
    (Clifford55AnomalyOSP.anomalyIndex 5 5 = 0) ∧
    cptSpectralMap (cptSpectralMap (1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
  constructor
  · exact anomalyIndex_55_zero_imported
  · simpa using cpt_spectral_map_sq (1 / 2 : ℂ)

theorem cartan_klein_bottle_geometry_synthesis (s : ℂ) (z : ℂ) :
    -- CPT is involutive
    cptSpectralMap (cptSpectralMap s) = s ∧
    -- Fixed locus = critical line
    (cptSpectralMap s = s ↔ s.re = 1/2) ∧
    -- Möbius V₄ identities
    mobiusJ (mobiusJ z) = z ∧
    mobiusGamma (mobiusGamma z) = z ∧
    mobiusJ (mobiusGamma z) = mobiusGamma (mobiusJ z) ∧
    -- Pin(5,5) anomaly index check
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 :=
  ⟨cpt_is_involution s,
   cpt_fixed_locus_is_critical_line s,
   mobiusJ_involutive z,
   mobiusGamma_involutive z,
   mobiusJ_gamma_commute z,
   anomalyIndex_55_zero_imported⟩

end CartanKleinBottleGeometry

end noncomputable section
