import InfoGeometry.Quantum.FourierTripartiteSlicing

namespace InfoGeometry.Canonical.FourierTripartiteSlicingCapstone

open InfoGeometry.Quantum.FourierTripartiteSlicing

theorem capstone_fourier_tripartite_synthesis
    {R : Type*} [CommRing R] [Algebra ℂ R] (X : R) (h : X^5 = X) :
    (P_vac X + P_sym X + P_anti X = 1) ∧
    (P_sym X * P_anti X = half * half * (X^8 - X^4)) ∧
    (P_sym X * P_anti X = 0) :=
  grand_fourier_tripartite_synthesis X h

end InfoGeometry.Canonical.FourierTripartiteSlicingCapstone
