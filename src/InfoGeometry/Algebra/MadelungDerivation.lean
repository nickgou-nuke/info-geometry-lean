import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace InfoGeometry.Algebra.MadelungDerivation

noncomputable section

variable {Base Carrier : Type*} [CommRing Base] [Field Carrier]
variable [Algebra Base Carrier]

def logarithmicDerivative (spatial : Derivation Base Carrier Carrier)
    (amplitude : Carrier) : Carrier :=
  spatial amplitude / amplitude

def amplitudeCurvature (spatial : Derivation Base Carrier Carrier)
    (amplitude : Carrier) : Carrier :=
  spatial (spatial amplitude) / amplitude

theorem curvature_eq_riccati (spatial : Derivation Base Carrier Carrier)
    (amplitude : Carrier) (amplitude_ne : amplitude ≠ 0) :
    amplitudeCurvature spatial amplitude =
      spatial (logarithmicDerivative spatial amplitude) +
        logarithmicDerivative spatial amplitude ^ 2 := by
  simp only [amplitudeCurvature, logarithmicDerivative, Derivation.leibniz_div,
    smul_eq_mul]
  field_simp
  ring

theorem logarithmicDerivative_square (spatial : Derivation Base Carrier Carrier)
    (amplitude : Carrier) :
    logarithmicDerivative spatial (amplitude ^ 2) =
      2 * logarithmicDerivative spatial amplitude := by
  by_cases amplitude_ne : amplitude = 0
  · simp [amplitude_ne, logarithmicDerivative]
  · simp only [logarithmicDerivative, Derivation.leibniz_pow, smul_eq_mul]
    norm_num
    field_simp

variable [CharZero Carrier]

theorem curvature_eq_density_score (spatial : Derivation Base Carrier Carrier)
    (amplitude : Carrier) (amplitude_ne : amplitude ≠ 0) :
    amplitudeCurvature spatial amplitude =
      spatial (logarithmicDerivative spatial (amplitude ^ 2)) / 2 +
        logarithmicDerivative spatial (amplitude ^ 2) ^ 2 / 4 := by
  rw [logarithmicDerivative_square, Derivation.leibniz]
  have constant : spatial (2 : Carrier) = 0 := spatial.map_natCast 2
  simp only [constant, smul_eq_mul, mul_zero, add_zero]
  rw [curvature_eq_riccati spatial amplitude amplitude_ne]
  ring

theorem curvature_eq_log_density (spatial : Derivation Base Carrier Carrier)
    (amplitude logDensity : Carrier) (amplitude_ne : amplitude ≠ 0)
    (log_derivative : spatial logDensity =
      logarithmicDerivative spatial (amplitude ^ 2)) :
    amplitudeCurvature spatial amplitude =
      spatial (spatial logDensity) / 2 + spatial logDensity ^ 2 / 4 := by
  rw [log_derivative]
  exact curvature_eq_density_score spatial amplitude amplitude_ne

def kineticEnergy (velocity : Carrier) : Carrier := velocity ^ 2 / 2

theorem derivative_kineticEnergy (spatial : Derivation Base Carrier Carrier)
    (velocity : Carrier) :
    spatial (kineticEnergy velocity) = velocity * spatial velocity := by
  have constant : spatial (2 : Carrier) = 0 := spatial.map_natCast 2
  rw [kineticEnergy, spatial.leibniz_div_const _ _ constant]
  simp only [Derivation.leibniz_pow, smul_eq_mul]
  norm_num
  ring

def hamiltonJacobiResidual (spatial temporal : Derivation Base Carrier Carrier)
    (phase potential : Carrier) : Carrier :=
  temporal phase + kineticEnergy (spatial phase) + potential

def eulerResidual (spatial temporal : Derivation Base Carrier Carrier)
    (velocity potential : Carrier) : Carrier :=
  temporal velocity + velocity * spatial velocity + spatial potential

theorem differentiate_hamiltonJacobi
    (spatial temporal : Derivation Base Carrier Carrier)
    (commute : Function.Commute spatial temporal) (phase potential : Carrier) :
    spatial (hamiltonJacobiResidual spatial temporal phase potential) =
      eulerResidual spatial temporal (spatial phase) potential := by
  simp only [hamiltonJacobiResidual, eulerResidual, map_add,
    derivative_kineticEnergy, commute phase]

theorem hamiltonJacobi_implies_euler
    (spatial temporal : Derivation Base Carrier Carrier)
    (commute : Function.Commute spatial temporal) (phase potential : Carrier)
    (hamiltonJacobi : hamiltonJacobiResidual spatial temporal phase potential = 0) :
    eulerResidual spatial temporal (spatial phase) potential = 0 := by
  rw [← differentiate_hamiltonJacobi spatial temporal commute, hamiltonJacobi, map_zero]

theorem quantum_euler
    (spatial temporal : Derivation Base Carrier Carrier)
    (commute : Function.Commute spatial temporal) (phase amplitude coupling : Carrier)
    (coupling_constant : spatial coupling = 0)
    (hamiltonJacobi : temporal phase + kineticEnergy (spatial phase) -
      coupling * amplitudeCurvature spatial amplitude = 0) :
    temporal (spatial phase) + spatial phase * spatial (spatial phase) =
      coupling * spatial (amplitudeCurvature spatial amplitude) := by
  have differentiated := congrArg spatial hamiltonJacobi
  simp only [map_sub, map_add, map_zero, derivative_kineticEnergy,
    Derivation.leibniz, smul_eq_mul, coupling_constant, mul_zero, add_zero,
    commute phase] at differentiated
  exact sub_eq_zero.mp differentiated

theorem amplitude_transport_implies_continuity
    (spatial temporal : Derivation Base Carrier Carrier)
    (amplitude velocity : Carrier)
    (transport : temporal amplitude + velocity * spatial amplitude +
      amplitude * spatial velocity / 2 = 0) :
    temporal (amplitude ^ 2) + spatial (amplitude ^ 2 * velocity) = 0 := by
  have scaled := congrArg (fun residual => 2 * amplitude * residual) transport
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
  norm_num
  linear_combination scaled

end

end InfoGeometry.Algebra.MadelungDerivation
