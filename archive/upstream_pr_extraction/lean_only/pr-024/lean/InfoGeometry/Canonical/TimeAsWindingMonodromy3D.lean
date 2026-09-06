import Mathlib
import InfoGeometry.Canonical.ChiralCausalConeFlow
import InfoGeometry.Canonical.DeterminantPhaseVolumeBridge
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.SouriauOperatorialLogPotential

/-!
# Time as logarithmic monodromy in 3D chiral cone geometry

\[
Q(X)=t^2-x^2-y^2-z^2,
\qquad
\partial Q = \{X\mid Q(X)=0\}.
\]

\[
\det(\mathrm{chiralMatrix}(X)) = Q(X),
\qquad
\mathrm{poleWinding}(R,h_R,n) \sim n\cdot 2\pi i.
\]
-/

noncomputable section

open Complex
open scoped Matrix

namespace InfoGeometry.Canonical.TimeAsWindingMonodromy3D

open InfoGeometry.Canonical.ChiralCausalConeFlow
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- `\mathrm{ChiralState}\,\mathbb R`. -/
abbrev Chiral3 := ChiralState ℝ

/-- `Q(X)`. -/
def lightconePotential (X : Chiral3) : ℝ :=
  causal_interval X

/-- `\partial Q := \{X\mid Q(X)=0\}`. -/
def lightconeBoundary : Set Chiral3 :=
  {X | lightconePotential X = 0}

/-- `\det\begin{psmallmatrix}t+z&x-iy\\x+iy&t-z\end{psmallmatrix}=Q(X)`. -/
def chiralMatrix (X : Chiral3) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(X.t + X.z : ℂ), (X.x - Complex.I * X.y : ℂ);
     (X.x + Complex.I * X.y : ℂ), (X.t - X.z : ℂ)]

theorem chiralMatrix_det (X : Chiral3) :
  Matrix.det (chiralMatrix X) = (lightconePotential X : ℂ) := by
  have hmul :
      (↑X.x + -(Complex.I * ↑X.y)) * (↑X.x + Complex.I * ↑X.y) =
        (↑X.x) ^ 2 + (↑X.y) ^ 2 := by
    calc
      (↑X.x + -(Complex.I * ↑X.y)) * (↑X.x + Complex.I * ↑X.y)
          = (↑X.x) ^ 2 - (Complex.I * ↑X.y) ^ 2 := by ring
      _ = (↑X.x) ^ 2 + (↑X.y) ^ 2 := by
        rw [mul_pow, Complex.I_sq]
        ring
  simp [lightconePotential, chiralMatrix, Matrix.det_fin_two, causal_interval, hmul, sub_eq_add_neg]
  ring_nf

theorem chiralPotential_eq_det (X : Chiral3) :
  (lightconePotential X : ℂ) = Matrix.det (chiralMatrix X) := by
  rw [chiralMatrix_det]

/-- `X\in\partial Q \iff \det(\mathrm{chiralMatrix}(X))=0`. -/
theorem boundary_eq_det_zero_iff (X : Chiral3) :
    X ∈ lightconeBoundary ↔ Matrix.det (chiralMatrix X) = 0 := by
  simp [lightconeBoundary, chiralMatrix_det]

/-- `S_+^2=S_-^2=0`. -/
def Splus : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 1; 0, 0]
def Sminus : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 0; 1, 0]

theorem Splus_sqr_eq_zero : Splus * Splus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Splus, Matrix.mul_apply]

theorem Sminus_sqr_eq_zero : Sminus * Sminus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Sminus, Matrix.mul_apply]

theorem Splus_det_zero : Matrix.det Splus = 0 := by
  simp [Splus, Matrix.det_fin_two]

theorem Sminus_det_zero : Matrix.det Sminus = 0 := by
  simp [Sminus, Matrix.det_fin_two]

/-- `\det(S_\pm)=0`. -/
theorem Splus_lightcone_singular : Matrix.det Splus = 0 := Splus_det_zero

theorem Sminus_lightcone_singular : Matrix.det Sminus = 0 := Sminus_det_zero

/-- `\mathrm{poleWinding}`. -/
def poleWinding (R : ℝ) (hR : 0 < R) (n : ℤ) : ℂ :=
  (n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)

/-- `\mathrm{poleWinding}=n\cdot 2\pi i`. -/
theorem poleWinding_eq_logarithmicPhase (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n = logarithmicPhase n := by
  unfold poleWinding
  simpa using (deRhamClass_of_winding (R := R) hR n)

/-- `\mathrm{poleWinding}/(2\pi i)=n`. -/
theorem poleWinding_index_is_integer (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num
  unfold poleWinding
  rw [deRhamClass_of_winding (R := R) hR n, logarithmicPhase, mul_assoc]
  field_simp [hI]

/-- `\partial Q \leftrightarrow \det(\mathrm{chiralMatrix})=0`. -/
def lightconeEntropyReadoutSupport : Prop :=
  ∀ X : Chiral3, X ∈ lightconeBoundary ↔ Matrix.det (chiralMatrix X) = 0

theorem lightcone_entropy_readout_support :
    lightconeEntropyReadoutSupport := by
  intro X
  exact boundary_eq_det_zero_iff X

/-- `\log\det` / volume-compression carrier. -/
noncomputable def lightconeBarrierCarrier :
    InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential Chiral3 :=
  { jacobian := fun _ => (1 : ℝ)
    logDetReg := fun X => Real.log (lightconePotential X)
    volumeCompressionPotential := fun X => -Real.log (lightconePotential X)
    volumeCompressionPotential_eq_neg_logDetReg := by
      intro X
      simp
    entropyReadoutRequiresStateClaim := lightconeEntropyReadoutSupport }

theorem lightconeBarrierCarrier_entropyReadoutRequiresStateClaim :
    lightconeBarrierCarrier.entropyReadoutRequiresStateClaim := by
  simpa [lightconeBarrierCarrier, lightconeEntropyReadoutSupport] using
    lightcone_entropy_readout_support

@[simp] theorem lightcone_barrier_equals_neg_logdet (X : Chiral3) :
    lightconeBarrierCarrier.volumeCompressionPotential X = -Real.log (lightconePotential X) := by
  simpa [lightconeBarrierCarrier] using
    (InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.volumeCompressionPotential_eq_neg_logDetReg_apply
      lightconeBarrierCarrier X)

/-- `Q(\mathrm{rindler\_boost}(X,\eta)) = Q(X)`. -/
theorem rindler_isometry [ModularTimeFlow ℝ] (X : Chiral3) (η : ℝ) :
    lightconePotential (rindler_boost X η) = lightconePotential X := by
  simpa [lightconePotential] using (rindler_flow_isometry (R := ℝ) X η)

/-- `\mathrm{TimeIsMonodromy}`. -/
class TimeIsMonodromy (ClockState : Type*) where
  clockCarrier : ClockState → Chiral3
  monodromyIndex : ClockState → ℤ → ℤ
  monodromyIndex_of_unit : ∀ c, monodromyIndex c 1 = 1

theorem time_tick_is_integer (ClockState : Type*) [TimeIsMonodromy ClockState]
    (c : ClockState) :
    TimeIsMonodromy.monodromyIndex (ClockState := ClockState) c 1 = 1 := by
  exact TimeIsMonodromy.monodromyIndex_of_unit c

end InfoGeometry.Canonical.TimeAsWindingMonodromy3D
