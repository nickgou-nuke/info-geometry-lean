/- Serre Exact Couple Construction -/

import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Spectral.Algebra.SpectralSequence

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Algebra.ExactCouple
open InfoGeometry.Spectral.Algebra

/- The Serre exact couple structure for a fibration F → E → B -/
/- Given a fibration F → E → B with fiber F and base B, and a spectrum Y,
   the long exact sequence in cohomology gives an exact couple where:
   D^{p,q} = H^{p+q}(E; Y) ⊕ H^{p+q}(F; Y)
   E^{p,q} = H^{p,q}(B; H^*(F; Y))
   The maps i, j, k come from the long exact sequence of the fibration. -/

structure SerreExactCoupleData (B F E : Type*) (Y : Spectrum) (R : Type u) [Ring R]
    (D E_ : Z2 → Type u)
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E_ pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E_ pq)] where
  (i : ∀ (pq : Z2), D pq →ₗ[R] D (shiftI pq))
  (j : ∀ (pq : Z2), D pq →ₗ[R] E_ pq)
  (k : ∀ (pq : Z2), E_ pq →ₗ[R] D (shiftK pq))
  (exact_k : ∀ (pq : Z2), LinearMap.ker (k pq) = LinearMap.range (j pq))

/- LEMMA 16: From a Serre exact couple data, we can construct an ExactCouple -/

def serre_exact_couple_from_data {B F E : Type*} (Y : Spectrum) (R : Type u) [Ring R]
    {D E_ : Z2 → Type u}
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E_ pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E_ pq)]
    (data : SerreExactCoupleData B F E Y R D E_) :
    ExactCouple R D E_ := by
  refine' ⟨
    fun pq => data.i pq,
    fun pq => data.j pq,
    fun pq => data.k pq,
    _⟩
  intro pq
  exact data.exact_k pq