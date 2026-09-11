import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

/-!
# Unimodular projective boundary pairs

Over a general commutative ring, a projective point is not an arbitrary
nonzero pair modulo cross-multiplication.  This owner uses unimodular pairs
and identifies them only by multiplication by a unit.
-/

abbrev UnimodularPair (R : Type*) [CommRing R] :=
  Subtype (fun p : R × R => ∃ a b : R, a * p.1 + b * p.2 = 1)

namespace UnimodularPair

abbrev fst {R : Type*} [CommRing R] (p : UnimodularPair R) : R := p.1.1
abbrev snd {R : Type*} [CommRing R] (p : UnimodularPair R) : R := p.1.2
abbrev unimodular {R : Type*} [CommRing R] (p : UnimodularPair R) :
    ∃ a b : R, a * p.fst + b * p.snd = 1 := p.2

end UnimodularPair

def unimodularPairRel {R : Type*} [CommRing R]
    (p q : UnimodularPair R) : Prop :=
  ∃ u : Rˣ,
    q.fst = (u : R) * p.fst ∧ q.snd = (u : R) * p.snd

instance unimodularPairSetoid (R : Type*) [CommRing R] :
    Setoid (UnimodularPair R) where
  r := unimodularPairRel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨1, by simp, by simp⟩
    · intro p q h
      rcases h with ⟨u, hfst, hsnd⟩
      refine ⟨u⁻¹, ?_, ?_⟩
      · rw [hfst]
        simp
      · rw [hsnd]
        simp
    · intro p q r hpq hqr
      rcases hpq with ⟨u, hqfst, hqsnd⟩
      rcases hqr with ⟨v, hrfst, hrsnd⟩
      refine ⟨v * u, ?_, ?_⟩
      · rw [hrfst, hqfst]
        simp [mul_assoc]
      · rw [hrsnd, hqsnd]
        simp [mul_assoc]

abbrev ProjectiveBoundary (R : Type*) [CommRing R] :=
  Quotient (unimodularPairSetoid R)

def projectiveBoundaryMk {R : Type*} [CommRing R]
    (p : UnimodularPair R) : ProjectiveBoundary R :=
  Quotient.mk' p

theorem projectiveBoundaryMk_eq_iff {R : Type*} [CommRing R]
    (p q : UnimodularPair R) :
    projectiveBoundaryMk p = projectiveBoundaryMk q ↔
      unimodularPairRel p q := by
  exact Quotient.eq_iff_equiv

def projectiveFixedPoint {R : Type*} [CommRing R]
    (f : UnimodularPair R → UnimodularPair R)
    (p : UnimodularPair R) : Prop :=
  unimodularPairRel p (f p)

theorem projectiveFixedPoint_iff_same_boundary {R : Type*} [CommRing R]
    (f : UnimodularPair R → UnimodularPair R)
    (p : UnimodularPair R) :
    projectiveFixedPoint f p ↔
      projectiveBoundaryMk p = projectiveBoundaryMk (f p) := by
  symm
  exact projectiveBoundaryMk_eq_iff p (f p)

end InfoGeometry.Topology
