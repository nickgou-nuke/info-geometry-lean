import InfoGeometry.Quantum.FourierTripartiteSlicing
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.FourierTripartiteSlicingCapstone

open InfoGeometry.Quantum.FourierTripartiteSlicing

theorem capstone_fourier_tripartite_synthesis
    {R : Type*} [CommRing R] [Algebra ℂ R] (X : R) (h : X ^ 5 = X) :
    (P_vac X + P_sym X + P_anti X = 1) ∧
    (P_sym X * P_anti X = half * half * (X ^ 8 - X ^ 4)) ∧
    (P_sym X * P_anti X = 0) := by
  exact ⟨completeness X, orthogonal_sym_anti X,
    orthogonal_sym_anti_of_X5_eq_X X h⟩

end InfoGeometry.Canonical.FourierTripartiteSlicingCapstone
