/- Serre Exact Couple Construction -/

import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/- LEMMA 16: Explicit maps satisfying all three exactness laws form an exact couple. -/

def serreExactCoupleOfMaps (R : Type u) [Ring R]
    {D E_ : Z2 → Type u}
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E_ pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E_ pq)]
    (i : ∀ pq, D pq →ₗ[R] D (shiftI pq))
    (j : ∀ pq, D pq →ₗ[R] E_ pq)
    (k : ∀ pq, E_ pq →ₗ[R] D (shiftK pq))
    (exact_ij :
      ∀ pq, LinearMap.ker (j (shiftI pq)) = LinearMap.range (i pq))
    (exact_jk :
      ∀ pq, LinearMap.ker (k pq) = LinearMap.range (j pq))
    (exact_ki :
      ∀ pq, LinearMap.ker (i (shiftK pq)) = LinearMap.range (k pq)) :
    ExactCouple R D E_ where
  i := i
  j := j
  k := k
  exact_ij := exact_ij
  exact_jk := exact_jk
  exact_ki := exact_ki

/--
Historical Serre exact-couple data name, now identified with the complete
native `ExactCouple` owner.

The former record duplicated the maps but carried only the `ker k = range j`
law.  A spectral exact couple requires all three exactness identities, so this
compatibility surface deliberately aliases the strengthened owner.
-/
abbrev SerreExactCoupleData
    (_B _F _Total : Type*) (_Y : Spectrum) (R : Type u) [Ring R]
    (D E_ : Z2 → Type u)
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E_ pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E_ pq)] :=
  ExactCouple R D E_

/--
Historical constructor name for the Serre exact couple.

Since `SerreExactCoupleData` is now the genuine complete owner, construction is
the identity rather than projection from an under-specified evidence record.
-/
def serre_exact_couple_from_data
    {B F Total : Type*} (Y : Spectrum) (R : Type u) [Ring R]
    {D E_ : Z2 → Type u}
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E_ pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E_ pq)]
    (data : SerreExactCoupleData B F Total Y R D E_) :
    ExactCouple R D E_ :=
  data
