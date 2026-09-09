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

theorem intoCarrier_smul (n : ℕ) (r : ℝ) (A : Stage n) :
    intoCarrier n (r • A) = r • intoCarrier n A := by
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (r • A) =
    r • InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A
  rw [Algebra.smul_def, Algebra.smul_def]
  change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
      (algebraMap ℝ (Stage n) r * A) =
    InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap r *
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A
  rw [InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap_stage n r]
  exact map_mul (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n) _ _

/-- Real phase plane element in stage `1 + k`. -/
def phasePlaneStage (k : ℕ) (s b : ℝ) : Stage (1 + k) :=
  s • (1 : Stage (1 + k)) + b • (finiteAdvance 1 k phaseAxisStage)

theorem phasePlane_intoCarrier (k : ℕ) (s b : ℝ) :
    intoCarrier (1 + k) (phasePlaneStage k s b) =
      s • (1 : CompatibleCarrier) + b • globalPhaseAxis := by
  unfold phasePlaneStage
  rw [map_add, intoCarrier_smul, intoCarrier_smul, map_one, phaseAxis_limit_image]

theorem phasePlaneStage_mul (k : ℕ) (s1 b1 s2 b2 : ℝ) :
    phasePlaneStage k s1 b1 * phasePlaneStage k s2 b2 =
      phasePlaneStage k (s1 * s2 - b1 * b2) (s1 * b2 + b1 * s2) := by
  unfold phasePlaneStage
  have hsq := phaseAxis_finiteAdvance_sq k
  have h1 (r : ℝ) (A : Stage (1 + k)) : (r • (1 : Stage (1 + k))) * A = r • A := by
    rw [Algebra.smul_mul_assoc, one_mul]
  have h2 (r : ℝ) (A : Stage (1 + k)) : A * (r • (1 : Stage (1 + k))) = r • A := by
    rw [mul_smul_comm, mul_one]
  have h3 (r1 r2 : ℝ) (A B : Stage (1 + k)) :
      (r1 • A) * (r2 • B) = (r1 * r2) • (A * B) := by
    rw [Algebra.smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [add_mul, mul_add, h1, h2, h3]
  rw [hsq]
  simp only [smul_neg, sub_eq_add_neg]
  module

theorem phasePlane_intoCarrier_conj_mul (k : ℕ) (s b : ℝ) :
    intoCarrier (1 + k) (phasePlaneStage k s b) *
        intoCarrier (1 + k) (phasePlaneStage k s (-b)) =
      (s ^ 2 + b ^ 2) • (1 : CompatibleCarrier) := by
  rw [← map_mul, phasePlaneStage_mul]
  have h1 : s * s - b * -b = s ^ 2 + b ^ 2 := by ring
  have h2 : s * -b + b * s = 0 := by ring
  rw [h1, h2, phasePlane_intoCarrier]
  simp

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
  unfold RealChiralPhase.phaseCurrent RealChiralPhase.chiralPhaseRate
  rw [mul_div_cancel₀ _ hρ]

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
  have h_prod1 : HasDerivAt (fun u => cosineQuadrature Phi u * dsin u)
      (dcos t * dsin t + cosineQuadrature Phi t * ddsin) t :=
    hcos.mul hdsin
  have h_prod2 : HasDerivAt (fun u => sineQuadrature Phi u * dcos u)
      (dsin t * dcos t + sineQuadrature Phi t * ddcos) t :=
    hsin.mul hdcos
  have h_sub : HasDerivAt (fun u => cosineQuadrature Phi u * dsin u - sineQuadrature Phi u * dcos u)
      (cosineQuadrature Phi t * ddsin - sineQuadrature Phi t * ddcos) t := by
    have h := h_prod1.sub h_prod2
    convert h using 1
    ring
  have h_mul := h_sub.const_mul (hbar / mass)
  exact h_mul

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
