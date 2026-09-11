import InfoGeometry.Quantum.ArtinBraidBostConnes
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ArtinBraidBostConnesCapstone

open InfoGeometry.Quantum.ArtinBraidBostConnes

theorem capstone_braid_galois_synthesis
    {A : Type*} [CommRing A] {R : Type*} [Ring R] [Algebra A R]
    (s : R) (q q_inv : A) (g : A →+* A)
    (hq : q_inv * q = 1) (h_hecke : HeckeRelation s q) :
    (s * (algebraMap A R q_inv * s - algebraMap A R (q_inv * (q - 1))) = 1) ∧
    (s * s = algebraMap A R (g q - 1) * s + algebraMap A R (g q) -
      algebraMap A R (g q - q) * (s + 1)) := by
  exact ⟨braid_inverse s q q_inv hq h_hecke,
    galois_hecke_shift s q g h_hecke⟩

end InfoGeometry.Canonical.ArtinBraidBostConnesCapstone
