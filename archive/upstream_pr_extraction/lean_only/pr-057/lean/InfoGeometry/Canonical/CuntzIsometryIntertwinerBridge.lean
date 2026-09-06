import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

/-!
# Cuntz isometry intertwining laws

These are the native consequences of the Toeplitz-Cuntz generator relations.
The file deliberately does not introduce a unitary endomorphism interface:
such an action requires separate data and is not implied by the generator
relations alone.
-/

namespace InfoGeometry.Canonical

namespace ToeplitzCuntzVacuumBridge.ToeplitzCuntzGenerators

variable {R : Type*} [Ring R] [StarRing R]

theorem pplus_mul_v1 (g : ToeplitzCuntzGenerators R) :
    PPlus g * g.V1 = g.V1 := by
  dsimp [PPlus]
  calc
    g.V1 * star g.V1 * g.V1 = g.V1 * (star g.V1 * g.V1) := by
      noncomm_ring
    _ = g.V1 := by rw [g.V1_isometry, mul_one]

theorem pminus_mul_v1 (g : ToeplitzCuntzGenerators R) :
    PMinus g * g.V1 = 0 := by
  dsimp [PMinus]
  calc
    g.V2 * star g.V2 * g.V1 = g.V2 * (star g.V2 * g.V1) := by
      noncomm_ring
    _ = 0 := by rw [g.V2_V1_orthogonal, mul_zero]

theorem v1_mul_pminus_factorization (g : ToeplitzCuntzGenerators R) :
    g.V1 * PMinus g = (g.V1 * g.V2) * star g.V2 := by
  dsimp [PMinus, QPlus]
  noncomm_ring

theorem qplus_mul_v2 (g : ToeplitzCuntzGenerators R) :
    QPlus g * g.V2 = g.V1 := by
  dsimp [QPlus]
  calc
    g.V1 * star g.V2 * g.V2 = g.V1 * (star g.V2 * g.V2) := by
      noncomm_ring
    _ = g.V1 := by rw [g.V2_isometry, mul_one]

theorem pminus_mul_v2 (g : ToeplitzCuntzGenerators R) :
    PMinus g * g.V2 = g.V2 := by
  dsimp [PMinus]
  calc
    g.V2 * star g.V2 * g.V2 = g.V2 * (star g.V2 * g.V2) := by
      noncomm_ring
    _ = g.V2 := by rw [g.V2_isometry, mul_one]

theorem pplus_mul_v2 (g : ToeplitzCuntzGenerators R) :
    PPlus g * g.V2 = 0 := by
  dsimp [PPlus]
  calc
    g.V1 * star g.V1 * g.V2 = g.V1 * (star g.V1 * g.V2) := by
      noncomm_ring
    _ = 0 := by rw [g.V1_V2_orthogonal, mul_zero]

theorem v2_mul_pplus_factorization (g : ToeplitzCuntzGenerators R) :
    g.V2 * PPlus g = (g.V2 * g.V1) * star g.V1 := by
  dsimp [PPlus, QMinus]
  noncomm_ring

theorem qminus_mul_v1 (g : ToeplitzCuntzGenerators R) :
    QMinus g * g.V1 = g.V2 := by
  dsimp [QMinus]
  calc
    g.V2 * star g.V1 * g.V1 = g.V2 * (star g.V1 * g.V1) := by
      noncomm_ring
    _ = g.V2 := by rw [g.V1_isometry, mul_one]

theorem isometry_intertwining_laws (g : ToeplitzCuntzGenerators R) :
    (PPlus g * g.V1 = g.V1) ∧
    (PMinus g * g.V1 = 0) ∧
    (g.V1 * PMinus g = (g.V1 * g.V2) * star g.V2) ∧
    (PMinus g * g.V2 = g.V2) ∧
    (PPlus g * g.V2 = 0) ∧
    (g.V2 * PPlus g = (g.V2 * g.V1) * star g.V1) ∧
    (QPlus g * g.V2 = g.V1) ∧
    (QMinus g * g.V1 = g.V2) := by
  exact ⟨pplus_mul_v1 g, pminus_mul_v1 g,
    v1_mul_pminus_factorization g, pminus_mul_v2 g, pplus_mul_v2 g,
    v2_mul_pplus_factorization g, qplus_mul_v2 g, qminus_mul_v1 g⟩

end ToeplitzCuntzVacuumBridge.ToeplitzCuntzGenerators

end InfoGeometry.Canonical
