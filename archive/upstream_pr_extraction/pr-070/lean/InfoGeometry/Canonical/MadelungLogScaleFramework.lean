import InfoGeometry.Arithmetic.CenteredXiTwinKernel
import InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow
import InfoGeometry.Clifford.Cl11InfiniteCarrier

/-!
# Finite-to-colimit Madelung phase carrier

This file composes the repository's existing real rotor coordinates with the
existing finite `Cl(1,1)` phase axis and its compatible direct-limit carrier.
It formalizes only the algebraic amplitude/phase transport.  No Schrodinger
operator, self-adjoint domain, or spectral identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.MadelungLogScaleFramework

open InfoGeometry.Geometry
open InfoGeometry.Algebraic
open InfoGeometry.Compatibility
open InfoGeometry.Arithmetic.CenteredXiTwinKernel
open InfoGeometry.Clifford.Cl11InfiniteCarrier

/-- The finite-to-colimit realization of the canonical scalar/bivector monoid. -/
def chiralPhaseLift (k : ℕ) : ChiralPhase →* CompatibleCarrier where
  toFun z :=
    intoCarrier (1 + k) (phasePlaneStage k z.scalar z.bivector)
  map_one' := by
    rw [phasePlane_intoCarrier]
    simp
  map_mul' z w := by
    rw [← map_mul]
    simpa using
      (congrArg (intoCarrier (1 + k))
        (phasePlaneStage_mul k z.scalar z.bivector w.scalar w.bivector)).symm

@[simp] theorem chiralPhaseLift_apply (k : ℕ) (z : ChiralPhase) :
    chiralPhaseLift k z =
      intoCarrier (1 + k) (phasePlaneStage k z.scalar z.bivector) :=
  rfl

theorem chiralPhaseLift_readout (k : ℕ) (z : ChiralPhase) :
    chiralPhaseLift k z =
      z.scalar • (1 : CompatibleCarrier) + z.bivector • globalPhaseAxis := by
  rw [chiralPhaseLift_apply, phasePlane_intoCarrier]

theorem chiralPhaseLift_conj_mul (k : ℕ) (z : ChiralPhase) :
    chiralPhaseLift k z * chiralPhaseLift k z.conj =
      z.normSq • (1 : CompatibleCarrier) := by
  rw [chiralPhaseLift_apply, chiralPhaseLift_apply]
  simpa [ChiralPhase.conj, ChiralPhase.normSq] using
    (phasePlane_intoCarrier_conj_mul k z.scalar z.bivector)

/-- The one-sided Hestenes ancestor has a canonical finite-to-colimit readout. -/
def hestenesAncestorLift (Phi : ℝ → ℝ) (t : ℝ) (k : ℕ) : CompatibleCarrier :=
  chiralPhaseLift k (realChiralPhaseEquiv (hestenesAncestor Phi t))

theorem hestenesAncestorLift_readout (Phi : ℝ → ℝ) (t : ℝ) (k : ℕ) :
    hestenesAncestorLift Phi t k =
      (hestenesAncestor Phi t).scalar • (1 : CompatibleCarrier) +
        (hestenesAncestor Phi t).bivector • globalPhaseAxis := by
  rw [hestenesAncestorLift, chiralPhaseLift_readout]
  simp only [realChiralPhaseEquiv_scalar, realChiralPhaseEquiv_bivector]

theorem hestenesAncestorLift_conj_mul
    (Phi : ℝ → ℝ) (t : ℝ) (k : ℕ) :
    hestenesAncestorLift Phi t k *
        chiralPhaseLift k ((realChiralPhaseEquiv (hestenesAncestor Phi t)).conj) =
      (RealChiralPhase.normSq (hestenesAncestor Phi t) : ℝ) •
        (1 : CompatibleCarrier) := by
  rw [hestenesAncestorLift]
  simpa only [realChiralPhaseEquiv_normSq] using
    (chiralPhaseLift_conj_mul k
      (realChiralPhaseEquiv (hestenesAncestor Phi t)))

theorem hestenesAncestor_phaseCurrent_readout
    (hbar mass : ℝ) (Phi : ℝ → ℝ) (t dcos dsin : ℝ) :
    RealChiralPhase.phaseCurrent hbar mass (hestenesAncestor Phi t)
        (dcos, dsin) =
      (hbar / mass) *
        (cosineQuadrature Phi t * dsin - sineQuadrature Phi t * dcos) := by
  rfl

/-! ## Native Madelung consequences -/

theorem hestenesAncestor_density_zero_iff
    (Phi : ℝ → ℝ) (t : ℝ) :
    RealChiralPhase.normSq (hestenesAncestor Phi t) = 0 ↔
      cosineQuadrature Phi t = 0 ∧ sineQuadrature Phi t = 0 := by
  exact RealChiralPhase.normSq_eq_zero_iff _

theorem hestenesAncestor_phaseRate_readout
    (Phi : ℝ → ℝ) (t dcos dsin : ℝ) :
    RealChiralPhase.chiralPhaseRate (hestenesAncestor Phi t) (dcos, dsin) =
      (cosineQuadrature Phi t * dsin - sineQuadrature Phi t * dcos) /
        (cosineQuadrature Phi t ^ 2 + sineQuadrature Phi t ^ 2) := by
  unfold RealChiralPhase.chiralPhaseRate RealChiralPhase.phaseNumerator
  rfl

theorem hestenesAncestor_phaseCurrent_eq_density_mul_phaseRate
    (hbar mass : ℝ) (Phi : ℝ → ℝ) (t dcos dsin : ℝ)
    (hρ : RealChiralPhase.normSq (hestenesAncestor Phi t) ≠ 0) :
    RealChiralPhase.phaseCurrent hbar mass (hestenesAncestor Phi t)
        (dcos, dsin) =
      (hbar / mass) *
        (RealChiralPhase.normSq (hestenesAncestor Phi t) *
          RealChiralPhase.chiralPhaseRate (hestenesAncestor Phi t) (dcos, dsin)) := by
  exact RealChiralPhase.phaseCurrent_eq_density_mul_phaseRate
    hbar mass (hestenesAncestor Phi t) (dcos, dsin) hρ

theorem hasDerivAt_hestenesAncestor_phaseCurrent
    (hbar mass : ℝ) (Phi : ℝ → ℝ)
    (dcos dsin : ℝ → ℝ) (ddcos ddsin t : ℝ)
    (hcos : HasDerivAt (cosineQuadrature Phi) (dcos t) t)
    (hsin : HasDerivAt (sineQuadrature Phi) (dsin t) t)
    (hdcos : HasDerivAt dcos ddcos t) (hdsin : HasDerivAt dsin ddsin t) :
    HasDerivAt
      (fun u => RealChiralPhase.phaseCurrent hbar mass
        (hestenesAncestor Phi u) (dcos u, dsin u))
      ((hbar / mass) *
        (cosineQuadrature Phi t * ddsin - sineQuadrature Phi t * ddcos)) t := by
  exact RealChiralPhase.hasDerivAt_phaseCurrent_of_components
    hbar mass (fun u => cosineQuadrature Phi u) (fun u => sineQuadrature Phi u)
    dcos dsin ddcos ddsin t hcos hsin hdcos hdsin

theorem hasDerivAt_hestenesAncestor_phaseCurrent_zero
    (hbar mass : ℝ) (Phi : ℝ → ℝ)
    (dcos dsin : ℝ → ℝ) (ddcos ddsin t : ℝ)
    (hcos : HasDerivAt (cosineQuadrature Phi) (dcos t) t)
    (hsin : HasDerivAt (sineQuadrature Phi) (dsin t) t)
    (hdcos : HasDerivAt dcos ddcos t) (hdsin : HasDerivAt dsin ddsin t)
    (hstationary : cosineQuadrature Phi t * ddsin =
      sineQuadrature Phi t * ddcos) :
    HasDerivAt
      (fun u => RealChiralPhase.phaseCurrent hbar mass
        (hestenesAncestor Phi u) (dcos u, dsin u)) 0 t := by
  have h := hasDerivAt_hestenesAncestor_phaseCurrent
    hbar mass Phi dcos dsin ddcos ddsin t hcos hsin hdcos hdsin
  convert h using 1
  rw [hstationary]
  ring

end InfoGeometry.Canonical.MadelungLogScaleFramework
