import InfoGeometry.Quantum.ComplexKramersAntiunitary
import InfoGeometry.Physics.ChiralEigenspaceEquivalence

noncomputable section

namespace InfoGeometry.Quantum.FiniteDIIIAntiunitary

abbrev Carrier := ComplexKramersAntiunitary.H2 × ComplexKramersAntiunitary.H2

def innerForm (first second : Carrier) : ℂ :=
  ComplexKramersAntiunitary.standardInner first.1 second.1 +
    ComplexKramersAntiunitary.standardInner first.2 second.2

def timeReversal : Carrier ≃ₗ⋆[ℂ] Carrier where
  toFun vector :=
    (ComplexKramersAntiunitary.timeReversal vector.1,
      ComplexKramersAntiunitary.timeReversal vector.2)
  invFun vector :=
    (ComplexKramersAntiunitary.timeReversal.symm vector.1,
      ComplexKramersAntiunitary.timeReversal.symm vector.2)
  left_inv vector := by simp
  right_inv vector := by simp
  map_add' first second := by simp
  map_smul' scalar vector := by simp

def particleHole : Carrier ≃ₗ⋆[ℂ] Carrier where
  toFun vector := (star vector.2, star vector.1)
  invFun vector := (star vector.2, star vector.1)
  left_inv vector := by simp
  right_inv vector := by simp
  map_add' first second := by simp
  map_smul' scalar vector := by simp [star_smul]

def hamiltonian : Module.End ℂ Carrier where
  toFun vector := (vector.1, -vector.2)
  map_add' first second := by simp [add_comm]
  map_smul' scalar vector := by simp

def chiral : Module.End ℂ Carrier :=
  Complex.I • (timeReversal.toLinearMap.comp particleHole.toLinearMap)

theorem timeReversal_sq (vector : Carrier) :
    timeReversal (timeReversal vector) = -vector := by
  apply Prod.ext <;> simp [timeReversal]

theorem particleHole_sq (vector : Carrier) :
    particleHole (particleHole vector) = vector := by
  simp [particleHole]

theorem timeReversal_antiunitary (first second : Carrier) :
    innerForm (timeReversal first) (timeReversal second) = innerForm second first := by
  exact congrArg₂ (· + ·)
    (ComplexKramersAntiunitary.timeReversal_antiunitary first.1 second.1)
    (ComplexKramersAntiunitary.timeReversal_antiunitary first.2 second.2)

theorem particleHole_antiunitary (first second : Carrier) :
    innerForm (particleHole first) (particleHole second) = innerForm second first := by
  simp [innerForm, particleHole, ComplexKramersAntiunitary.standardInner]
  ring

theorem timeReversal_particleHole_commute (vector : Carrier) :
    timeReversal (particleHole vector) = particleHole (timeReversal vector) := by
  apply Prod.ext <;> ext index <;> fin_cases index <;>
    simp [timeReversal, particleHole, ComplexKramersAntiunitary.timeReversal]

theorem hamiltonian_timeReversal (vector : Carrier) :
    hamiltonian (timeReversal vector) = timeReversal (hamiltonian vector) := by
  simp [hamiltonian, timeReversal]

theorem hamiltonian_particleHole (vector : Carrier) :
    hamiltonian (particleHole vector) = -particleHole (hamiltonian vector) := by
  simp [hamiltonian, particleHole]

theorem hamiltonian_selfAdjoint (first second : Carrier) :
    innerForm (hamiltonian first) second = innerForm first (hamiltonian second) := by
  simp [innerForm, hamiltonian, ComplexKramersAntiunitary.standardInner]

theorem hamiltonian_sq : hamiltonian.comp hamiltonian = LinearMap.id := by
  apply LinearMap.ext
  intro vector
  simp [hamiltonian]

theorem hamiltonian_kernel : LinearMap.ker hamiltonian = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro first second hequal
  have htwice := congrArg hamiltonian hequal
  simpa [hamiltonian] using htwice

theorem chiral_sq : chiral.comp chiral = LinearMap.id := by
  apply LinearMap.ext
  intro vector
  apply Prod.ext <;> ext index <;> fin_cases index <;>
    simp [chiral, timeReversal, particleHole, ComplexKramersAntiunitary.timeReversal,
      ← mul_assoc]

theorem hamiltonian_chiral :
    hamiltonian.comp chiral = -(chiral.comp hamiltonian) := by
  apply LinearMap.ext
  intro vector
  apply Prod.ext <;> ext index <;> fin_cases index <;>
    simp [hamiltonian, chiral, timeReversal, particleHole, ComplexKramersAntiunitary.timeReversal]

def pairedEigenspaces (eigenvalue : ℂ) :
    hamiltonian.eigenspace eigenvalue ≃ₗ[ℂ] hamiltonian.eigenspace (-eigenvalue) :=
  InfoGeometry.Physics.ChiralEigenspaceEquivalence.eigenspaceEquiv
    hamiltonian chiral hamiltonian_chiral chiral_sq eigenvalue

theorem real_eigenvalue_kramers_partner (eigenvalue : ℝ) (vector : Carrier)
    (heigen : hamiltonian vector = (eigenvalue : ℂ) • vector) :
    hamiltonian (timeReversal vector) = (eigenvalue : ℂ) • timeReversal vector := by
  rw [hamiltonian_timeReversal, heigen, map_smulₛₗ]
  simp

end InfoGeometry.Quantum.FiniteDIIIAntiunitary
