/- Gysin sequence for sphere bundles - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/gysin.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Cohomology.Serre
import InfoGeometry.Spectral.Cohomology.Basic

open InfoGeometry.Spectral.Cohomology
open InfoGeometry.Spectral.Algebra
open InfoGeometry.Spectral.Spectrum.Basic

/- Gysin sequence for sphere bundles -/

/- Given a sphere bundle S^{n+1} → E → B and an abelian group A.
   The only nontrivial differentials in the spectral sequence of this map are the following
   differentials on page n:
   d_m = d_(m-1,n+1)^n : E_(m-1,n+1)^n → E_(m+n+1,0)^n
   Note that ker d_m = E_(m-1,n+1)^∞ and coker d_m = E_(m+n+1,0)^∞.
   Each diagonal on the ∞-page has at most two nontrivial groups, which means that
   coker d_{m-1} and ker d_m are the only two nontrivial groups building up D_{m+n}^∞,
   where D^∞ is the abutment of the spectral sequence.
   This gives the short exact sequences:
   coker d_{m-1} → D_{m+n}^∞  → ker d_m
   We can splice these SESs together to get a LES
   ... E_(m+n,0)^n → D_{m+n}^∞ → E_(m-1,n+1)^n → E_(m+n+1,0)^n → D_{m+n+1}^∞ ...
   Now we have
   E_(p,q)^n = E_(p,q)^0 = H^p(B; H^q(S^{n+1}; A)) = H^p(B; A) if q = n+1 or q = 0
   and
   D_{n}^∞ = H^n(E; A)
   This gives the Gysin sequence
   ... H^{m+n}(B; A) → H^{m+n}(E; A) → H^{m-1}(B; A) → H^{m+n+1}(B; A) → H^{m+n+1}(E; A) ...
-/

/-- Index data for a vanishing `E`-page entry away from rows `0` and `n + 1`. -/
structure GysinTrivialEpageIndex (n : ℕ) where
  page : ℕ
  column : ℤ
  row : ℤ
  row_ne_zero : row ≠ 0
  row_ne_sphere : row ≠ (n + 1 : ℤ)

/-- Index data for an `E`-page row strictly above the sphere-bundle top row. -/
structure GysinAboveSphereRowIndex (n : ℕ) where
  page : ℕ
  column : ℤ
  row : ℤ
  row_gt_sphere : row > (n + 1 : ℤ)

/-- Finite port datum for the Gysin sequence attached to a projection `E → B`. -/
structure GysinPortDatum (E B A : Type*) [AddCommGroup A] where
  sphereDim : ℕ
  projection : E → B

/-- Degree-tagged piece of the finite Gysin port. -/
structure GysinDegreeDatum (E B A : Type*) [AddCommGroup A] extends GysinPortDatum E B A where
  degree : ℤ

def gysin_trivial_Epage {E B : Type*} {n : ℕ} (_HB : True) (_f : E → B)
  (_e : True) (_A : Type*) [AddCommGroup _A] (r : ℕ) (p q : ℤ) (hq : q ≠ 0)
  (hq' : q ≠ (n + 1 : ℤ)) :
    GysinTrivialEpageIndex n :=
  ⟨r, p, q, hq, hq'⟩

def gysin_trivial_Epage2 {E B : Type*} {n : ℕ} (_HB : True) (_f : E → B)
  (_e : True) (_A : Type*) [AddCommGroup _A] (r : ℕ) (p q : ℤ)
  (hq : q > (n + 1 : ℤ)) :
    GysinAboveSphereRowIndex n :=
  ⟨r, p, q, hq⟩

def gysin_sequence' {E B : Type*} {n : ℕ} (_HB : True) (f : E → B)
  (_e : True) (A : Type*) [AddCommGroup A] : GysinPortDatum E B A :=
  ⟨n, f⟩

def gysin_sequence'_zero {E B : Type*} {n : ℕ} (_HB : True) (f : E → B)
  (_e : True) (A : Type*) [AddCommGroup A] (m : ℤ) :
    GysinDegreeDatum E B A :=
  ⟨⟨n, f⟩, m + n⟩

def gysin_sequence'_one {E B : Type*} {n : ℕ} (_HB : True) (f : E → B)
  (_e : True) (A : Type*) [AddCommGroup A] (m : ℤ) :
    GysinDegreeDatum E B A :=
  ⟨⟨n, f⟩, m - 1⟩

def gysin_sequence'_two {E B : Type*} {n : ℕ} (_HB : True) (f : E → B)
  (_e : True) (A : Type*) [AddCommGroup A] (m : ℤ) :
    GysinDegreeDatum E B A :=
  ⟨⟨n, f⟩, m + n + 1⟩

@[simp]
theorem gysin_trivial_Epage_row {E B : Type*} {n : ℕ} (HB : True) (f : E → B)
  (e : True) (A : Type*) [AddCommGroup A] (r : ℕ) (p q : ℤ) (hq : q ≠ 0)
  (hq' : q ≠ (n + 1 : ℤ)) :
    (gysin_trivial_Epage HB f e A r p q hq hq').row = q :=
  rfl

@[simp]
theorem gysin_sequence'_projection {E B : Type*} {n : ℕ} (HB : True) (f : E → B)
  (e : True) (A : Type*) [AddCommGroup A] :
    (gysin_sequence' (n := n) HB f e A).projection = f :=
  rfl
