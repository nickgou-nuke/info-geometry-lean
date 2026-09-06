import InfoGeometry.Algebra.BostConnesGalois

namespace InfoGeometry.Canonical.BostConnesGaloisCapstone

open InfoGeometry.Algebra.BostConnesGalois

theorem capstone_bost_connes_galois_synthesis (g : ℤ) (n : ℕ) (r : ℚ) :
    (galoisAction g (semigroupEndo n r) = semigroupEndo n (galoisAction g r)) ∧
    (‖cyclotomicPhase r‖ = 1) :=
  grand_bost_connes_galois_synthesis g n r

end InfoGeometry.Canonical.BostConnesGaloisCapstone
