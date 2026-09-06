import Mathlib.Analysis.InnerProductSpace.Spectrum
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Krein.DoubledSpace

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.HestenesPhaseSpectral

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => InfoGeometry.Krein.clockAxis (E := E)

/-- Naming alias: Hestenes-linear operators are phase-linear for `K = clockAxis`. -/
@[rep_depth krein] abbrev IsHestenesLinear (A : EndH) : Prop := IsPhaseLinear (E := E) A

/-- Naming alias: Hestenes-antilinear operators are phase-antilinear for `K = clockAxis`. -/
@[rep_depth krein] abbrev IsHestenesAntilinear (A : EndH) : Prop := IsPhaseAntilinear (E := E) A

/--
Core doubled-real spectral seed:
if `A` commutes with the phase axis `K` and `v` is a real eigenvector of `A`
with eigenvalue `λ`, then `K v` is again a `λ`-eigenvector.
-/
theorem eigenvector_phaseAxis_of_hestenesLinear
    (A : EndH)
    (hA : IsHestenesLinear (E := E) A)
    (lam : ℝ)
    {v : H₂}
    (hv : A v = lam • v) :
    A (Kop v) = lam • (Kop v) := by
  have hComm : Commute A Kop :=
    commute_clockAxis_of_IsPhaseLinear (E := E) hA
  calc
    A (Kop v) = Kop (A v) := by
      simpa [ContinuousLinearMap.comp_apply, Commute] using congrArg (fun T : EndH => T v) hComm
    _ = Kop (lam • v) := by simp [hv]
    _ = lam • (Kop v) := by simp

/--
Eigenvector predicate on the doubled real carrier.
-/
def IsEigenvector (A : EndH) (lam : ℝ) (v : H₂) : Prop :=
  A v = lam • v

/--
Equivalent eigenspace-stability form phrased without spectral-measure machinery.
-/
theorem eigenspace_phaseAxis_stable_of_hestenesLinear
    (A : EndH)
    (hA : IsHestenesLinear (E := E) A)
    (lam : ℝ)
    {v : H₂}
    (hv : IsEigenvector (E := E) A lam v) :
    IsEigenvector (E := E) A lam (Kop v) := by
  exact eigenvector_phaseAxis_of_hestenesLinear (E := E) A hA lam hv

/--
Submodule-level form: `K = clockAxis` maps the real eigenspace of `A` at `lam`
into itself whenever `A` is Hestenes-linear.
-/
theorem phaseAxis_mapsTo_eigenspace_of_hestenesLinear
    (A : EndH)
    (hA : IsHestenesLinear (E := E) A)
    (lam : ℝ) :
    Set.MapsTo Kop (Module.End.eigenspace (A.toLinearMap) lam)
      (Module.End.eigenspace (A.toLinearMap) lam) := by
  intro v hv
  have hv' : A v = lam • v := by
    simpa [Module.End.mem_eigenspace_iff] using hv
  have hKv : A (Kop v) = lam • (Kop v) :=
    eigenvector_phaseAxis_of_hestenesLinear (E := E) A hA lam hv'
  exact (Module.End.mem_eigenspace_iff).2 hKv


/--
Commuting antilinear symmetry preserves real eigenspaces.
Here antilinearity is encoded as phase-antilinearity relative to `K`.
-/
theorem commuting_antilinear_preserves_real_eigenspace
    (A C : EndH)
    (lam : ℝ)
    (_hC : IsHestenesAntilinear (E := E) C)
    (hCA : C.comp A = A.comp C)
    {v : H₂}
    (hv : A v = lam • v) :
    A (C v) = lam • (C v) := by
  have hComm_apply : C (A v) = A (C v) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T v) hCA
  calc
    A (C v) = C (A v) := hComm_apply.symm
    _ = C (lam • v) := by simp [hv]
    _ = lam • (C v) := by simp

/--
Anticommuting antilinear symmetry flips real eigenvalues:
if `C A = - A C` and `A v = λ v`, then `A (C v) = (-λ) (C v)`.
-/
theorem anticommuting_antilinear_flips_real_eigenvalue
    (A C : EndH)
    (lam : ℝ)
    (_hC : IsHestenesAntilinear (E := E) C)
    (hCA : C.comp A = -(A.comp C))
    {v : H₂}
    (hv : A v = lam • v) :
    A (C v) = (-lam) • (C v) := by
  have hComm_apply : C (A v) = - (A (C v)) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T v) hCA
  have hA_Cv : A (C v) = -(C (A v)) := by
    have hneg := congrArg Neg.neg hComm_apply
    simpa [neg_neg] using hneg.symm
  calc
    A (C v) = - C (A v) := hA_Cv
    _ = - C (lam • v) := by simp [hv]
    _ = (-lam) • (C v) := by simp


/-- Phase-linearity is stable under operator composition. -/
theorem isPhaseLinear_comp
    (A B : EndH)
    (hA : IsPhaseLinear (E := E) A)
    (hB : IsPhaseLinear (E := E) B) :
    IsPhaseLinear (E := E) (A.comp B) := by
  unfold IsPhaseLinear at *
  calc
    (A.comp B).comp (InfoGeometry.Krein.clockAxis (E := E))
        = A.comp (B.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp ((InfoGeometry.Krein.clockAxis (E := E)).comp B) := by rw [hB]
    _ = (A.comp (InfoGeometry.Krein.clockAxis (E := E))).comp B := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = ((InfoGeometry.Krein.clockAxis (E := E)).comp A).comp B := by rw [hA]
    _ = (InfoGeometry.Krein.clockAxis (E := E)).comp (A.comp B) := by
          simp [ContinuousLinearMap.comp_assoc]

/-! The phase-linear carrier is also stable under Hilbert adjunction. -/

theorem isPhaseLinear_adjoint
    (A : EndH)
    (hA : IsPhaseLinear (E := E) A) :
    IsPhaseLinear (E := E) (ContinuousLinearMap.adjoint A) := by
  unfold IsPhaseLinear at *
  have h := congrArg ContinuousLinearMap.adjoint hA
  simpa [ContinuousLinearMap.adjoint_comp,
    InfoGeometry.Krein.complex_i_adjoint_eq_neg,
    InfoGeometry.Krein.clockAxis_eq_complex_i] using h.symm

/-! Real scalar multiples remain in the phase-linear carrier. -/

theorem isPhaseLinear_smul
    (c : ℝ) (A : EndH)
    (hA : IsPhaseLinear (E := E) A) :
    IsPhaseLinear (E := E) (c • A) := by
  unfold IsPhaseLinear at *
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hA]

/-! The Cayley complex scalar action on the phase-linear carrier. -/

noncomputable def cayleyPhaseSmul (z : ℂ) (A : EndH) : EndH :=
  z.re • A + z.im • ((InfoGeometry.Krein.clockAxis (E := E)).comp A)

private theorem isPhaseLinear_add_local
    (A B : EndH)
    (hA : IsPhaseLinear (E := E) A)
    (hB : IsPhaseLinear (E := E) B) :
    IsPhaseLinear (E := E) (A + B) := by
  unfold IsPhaseLinear at *
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hA, hB]

theorem cayleyPhaseSmul_isPhaseLinear
    (z : ℂ) (A : EndH)
    (hA : IsPhaseLinear (E := E) A) :
    IsPhaseLinear (E := E) (cayleyPhaseSmul (E := E) z A) := by
  unfold cayleyPhaseSmul
  apply isPhaseLinear_add_local
  · exact isPhaseLinear_smul (E := E) z.re A hA
  · apply isPhaseLinear_smul (E := E) z.im
    apply isPhaseLinear_comp (E := E) Kop A
    · unfold IsPhaseLinear
      rfl
    · exact hA

@[simp] theorem cayleyPhaseSmul_one (A : EndH) :
    cayleyPhaseSmul (E := E) 1 A = A := by
  dsimp [cayleyPhaseSmul]
  have hzero : (0 : ℝ) • complex_i.comp A = 0 := by
    ext x
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, zero_smul]
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, zero_smul]
  rw [one_smul, hzero, add_zero]

/--
Projector compatibility interface: any projector commuting with `K = clockAxis` is Hestenes-linear.
-/
theorem spectral_projector_isHestenesLinear
    (P : EndH)
    (hProjComm :
      P.comp (InfoGeometry.Krein.clockAxis (E := E)) =
        (InfoGeometry.Krein.clockAxis (E := E)).comp P) :
    IsHestenesLinear (E := E) P := by
  simpa [IsHestenesLinear, IsPhaseLinear] using hProjComm

/--
Owner-property bridge: a property conformal/Drazin spectral projector on the doubled
carrier is Hestenes-linear as soon as clock-axis commutation is property.
-/
theorem propertyConformal_spectralProjector_isHestenesLinear
    (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference H₂)
    (hProjComm :
      CCI.spectralProjector.comp (InfoGeometry.Krein.clockAxis (E := E)) =
        (InfoGeometry.Krein.clockAxis (E := E)).comp CCI.spectralProjector) :
    IsHestenesLinear (E := E) CCI.spectralProjector := by
  exact spectral_projector_isHestenesLinear (E := E) CCI.spectralProjector hProjComm

/--
Equivalent owner-property bridge in phase-linear form.
-/
theorem propertyConformal_spectralProjector_isHestenesLinear_of_IsPhaseLinear
    (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference H₂)
    (hPhase : IsPhaseLinear (E := E) CCI.spectralProjector) :
    IsHestenesLinear (E := E) CCI.spectralProjector := by
  exact hPhase

/--
Owner-property closure: if both `A` and `A_D` are phase-linear, then the property
Drazin spectral projector `P = A * A_D` is phase-linear (hence Hestenes-linear).
-/
theorem propertyConformal_spectralProjector_isHestenesLinear_of_IsPhaseLinear_factors
    (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference H₂)
    (hA_phase : IsPhaseLinear (E := E) CCI.A)
    (hAD_phase : IsPhaseLinear (E := E) CCI.A_D) :
    IsHestenesLinear (E := E) CCI.spectralProjector := by
  have hP_phase : IsPhaseLinear (E := E) (CCI.A.comp CCI.A_D) :=
    isPhaseLinear_comp (E := E) CCI.A CCI.A_D hA_phase hAD_phase
  simpa [InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.spectralProjector,
    InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.toCertifiedInverseKernel,
    InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector,
    InfoGeometry.Canonical.CertifiedInverseKernel.toInverseKernel',
    InfoGeometry.Canonical.InverseKernel.spectralProjector,
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection] using hP_phase

/--
`A` is phase-linear under a compatible Drazin/Krein/chiral package on `(A, A_D)`.
-/
theorem propertyConformal_A_isPhaseLinear_of_kreinCompat
    (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference H₂)
    (hCompat :
      InfoGeometry.Canonical.DrazinKreinCompatibility.KreinGradedDrazinCompatibility
        (E := E) CCI.A CCI.A_D CCI.drazinIndex) :
    IsPhaseLinear (E := E) CCI.A := by
  unfold IsPhaseLinear
  change CCI.A.comp (InfoGeometry.Krein.complex_i (E := E)) =
    (InfoGeometry.Krein.complex_i (E := E)).comp CCI.A
  calc
    CCI.A.comp (InfoGeometry.Krein.complex_i (E := E))
        = CCI.A.comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by rfl
    _ = (CCI.A.comp (modular_j (E := E))).comp (spectral_epsilon (E := E)) := by rfl
    _ = ((modular_j (E := E)).comp CCI.A).comp (spectral_epsilon (E := E)) := by
          rw [hCompat.J_comm_T]
    _ = (modular_j (E := E)).comp (CCI.A.comp (spectral_epsilon (E := E))) := by rfl
    _ = (modular_j (E := E)).comp ((spectral_epsilon (E := E)).comp CCI.A) := by
          rw [hCompat.ε_comm_T]
    _ = (InfoGeometry.Krein.complex_i (E := E)).comp CCI.A := by rfl

/--
`A_D` is phase-linear under a compatible Drazin/Krein/chiral package on `(A, A_D)`.
-/
theorem propertyConformal_AD_isPhaseLinear_of_kreinCompat
    (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference H₂)
    (hCompat :
      InfoGeometry.Canonical.DrazinKreinCompatibility.KreinGradedDrazinCompatibility
        (E := E) CCI.A CCI.A_D CCI.drazinIndex) :
    IsPhaseLinear (E := E) CCI.A_D := by
  unfold IsPhaseLinear
  change CCI.A_D.comp (InfoGeometry.Krein.complex_i (E := E)) =
    (InfoGeometry.Krein.complex_i (E := E)).comp CCI.A_D
  calc
    CCI.A_D.comp (InfoGeometry.Krein.complex_i (E := E))
        = CCI.A_D.comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by rfl
    _ = (CCI.A_D.comp (modular_j (E := E))).comp (spectral_epsilon (E := E)) := by rfl
    _ = ((modular_j (E := E)).comp CCI.A_D).comp (spectral_epsilon (E := E)) := by
          rw [hCompat.J_comm_TD]
    _ = (modular_j (E := E)).comp (CCI.A_D.comp (spectral_epsilon (E := E))) := by rfl
    _ = (modular_j (E := E)).comp ((spectral_epsilon (E := E)).comp CCI.A_D) := by
          rw [hCompat.ε_comm_TD]
    _ = (InfoGeometry.Krein.complex_i (E := E)).comp CCI.A_D := by rfl

/--
Fully automatic owner-property closure: once the property conformal package is
upgraded with Drazin/Krein/chiral compatibility on `(A, A_D)`, phase-linearity
of the property spectral projector follows with no extra hypotheses.
-/
theorem propertyConformal_spectralProjector_isHestenesLinear_of_kreinCompat
    (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference H₂)
    (hCompat :
      InfoGeometry.Canonical.DrazinKreinCompatibility.KreinGradedDrazinCompatibility
        (E := E) CCI.A CCI.A_D CCI.drazinIndex) :
    IsHestenesLinear (E := E) CCI.spectralProjector := by
  exact propertyConformal_spectralProjector_isHestenesLinear_of_IsPhaseLinear_factors
    (E := E) CCI
    (propertyConformal_A_isPhaseLinear_of_kreinCompat (E := E) CCI hCompat)
    (propertyConformal_AD_isPhaseLinear_of_kreinCompat (E := E) CCI hCompat)

section FiniteProjector

variable [FiniteDimensional ℝ E]

/--
Canonical finite-dimensional orthogonal projector onto a real subspace of the doubled carrier.
-/
noncomputable abbrev orthogonalSubspaceProjector
    (U : Submodule ℝ H₂) : EndH :=
  U.subtypeL.comp (Submodule.orthogonalProjection U).toContinuousLinearMap

/--
Orthogonal-subspace specialization of `spectral_projector_isHestenesLinear`.
-/
theorem orthogonalSubspaceProjector_isHestenesLinear
    (U : Submodule ℝ H₂)
    (hProjComm :
      (orthogonalSubspaceProjector (E := E) U).comp (InfoGeometry.Krein.clockAxis (E := E)) =
        (InfoGeometry.Krein.clockAxis (E := E)).comp (orthogonalSubspaceProjector (E := E) U)) :
    IsHestenesLinear (E := E) (orthogonalSubspaceProjector (E := E) U) := by
  exact spectral_projector_isHestenesLinear (E := E)
    (orthogonalSubspaceProjector (E := E) U) hProjComm

end FiniteProjector

end Core

end InfoGeometry.Canonical.HestenesPhaseSpectral
