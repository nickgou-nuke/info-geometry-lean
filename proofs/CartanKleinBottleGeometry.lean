import proofs.MobiusCantorTKKClosure
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import proofs.Clifford55AnomalyOSP
import proofs.MajoranaPrimonSpectralBridge

/-!
# Cartan/Klein Algebraic Checks

This file records finite algebraic identities used by the surrounding
Cartan/Klein discussion.  It does not prove a quotient-space
identification or any analytic/global geometric classification theorem.

Finite facts proved here:
1. the CPT spectral map is involutive
2. its fixed locus is the critical line Re(s)=½
3. the Möbius maps J(z)=z⁻¹ and Γ(z)=-z satisfy V₄ identities
4. the split anomaly index satisfies anomalyIndex 5 5 = 0

Zero sorries.
-/

noncomputable section

namespace CartanKleinBottleGeometry

open MobiusCantorTKKClosure
open ProjectiveAffineConformalClosure55
open MajoranaPrimonSpectralBridge
open Clifford55AnomalyOSP

/-! ## 1. CPT as an involution with fixed line -/

/-- A finite involutive map together with its stated fixed set. -/
structure SpectralInvolution (V : Type*) where
  theta : V → V
  involutive : ∀ v, theta (theta v) = v
  fixedLocus : Set V

/-- The CPT spectral map is an involution on ℂ. -/
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

/-! ## 2. CPT square and fixed-line algebra -/

/-- Applying the CPT spectral map twice returns the original point. -/
theorem cpt_spectral_map_sq (s : ℂ) :
    cptSpectralMap (cptSpectralMap s) = s :=
  cptSpectralInvolution.involutive s

/-- A point is fixed by the CPT spectral map exactly on Re(s)=½. -/
theorem critical_line_is_cpt_fixed_line (s : ℂ) :
    cptSpectralMap s = s ↔ s.re = 1/2 :=
  cpt_fixed_point_iff_critical_line s

/-! ## 3. Split anomaly and V₄ identities -/

/-- The split anomaly index for Pin(5,5) vanishes.
This theorem imports the finite equality anomalyIndex 5 5 = 0. -/
theorem anomalyIndex_55_zero_imported :
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 :=
  Clifford55AnomalyOSP.anomalyIndex_55_zero

/-- The Möbius V₄ involutions J(z)=z⁻¹ and Γ(z)=-z satisfy the
imported order-two and commutation identities. -/
theorem mobius_v4_identities (z : ℂ) :
    mobiusJ (mobiusJ z) = z ∧
    mobiusGamma (mobiusGamma z) = z ∧
    mobiusJ (mobiusGamma z) = mobiusGamma (mobiusJ z) :=
  ⟨mobiusJ_involutive z, mobiusGamma_involutive z, mobiusJ_gamma_commute z⟩

/-! ## 4. Combined finite checks -/

/-- A combined finite check: the anomaly index vanishes and CPT fixes 1/2. -/
theorem cartan_symmetric_space_finite_check :
    (Clifford55AnomalyOSP.anomalyIndex 5 5 = 0) ∧
    cptSpectralMap (cptSpectralMap (1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
  constructor
  · exact anomalyIndex_55_zero_imported
  · simpa using cpt_spectral_map_sq (1 / 2 : ℂ)

/-! ## 5. Synthesis of finite algebraic facts -/

/-- Synthesis of the finite algebraic identities available in this file. -/
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
