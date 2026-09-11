import InfoGeometry.Krein.DoubledSpaceMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11Matrix

open scoped Matrix

namespace InfoGeometry.Clifford.MatrixCompat

open InfoGeometry.Clifford.Cl11Matrix

/-- Canonical base symmetry for the Kronecker tower. -/
noncomputable def baseJ1 : Matrix (Fin 2) (Fin 2) ℝ := J1

lemma baseJ1_sq : baseJ1 * baseJ1 = 1 := by
  simpa [baseJ1] using J1_sq

lemma baseJ1_transpose : baseJ1ᵀ = baseJ1 := by
  simpa [baseJ1] using J1_transpose

end InfoGeometry.Clifford.MatrixCompat
