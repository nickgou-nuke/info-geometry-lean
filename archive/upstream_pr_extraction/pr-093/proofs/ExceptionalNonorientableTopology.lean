import Mathlib

/-!
# Exceptional topology on nonorientable manifolds

Digest source: arXiv:2503.04889v2,
J. Lukas K. König et al., *Exceptional topology on nonorientable manifolds*.

The paper classifies non-Hermitian eigenvalue-braid phases on nonorientable
2D parameter spaces such as the Klein bottle `K²` and real projective plane
`RP²`. The core algebraic constraints are:

* Klein bottle gapped phases: `Bq * Bp * Bq⁻¹ * Bp = 1`;
* projective-plane gapped phases: `Bpq^2 = 1`;
* after abelianization, these become torsion equations `2 Ap = 0` and
  `2 Apq = 0`;
* for two-band systems `B₂ ≅ ℤ`, torsion-freeness forces those abelianized
  gapped invariants to vanish;
* in gapless systems the total EP charge is allowed to be the corresponding
  nonorientable relator word, producing nonorientable charge-inversion and
  fermion-doubling violation.
-/

noncomputable section

namespace ExceptionalNonorientableTopology

/-! ## Abstract braid-word constraints -/

variable {G : Type} [Group G]

/-- Klein bottle relator word: `q p q⁻¹ p`. -/
def kleinWord (q p : G) : G := q * p * q⁻¹ * p

/-- Torus commutator word, included for contrast. -/
def torusCommutator (q p : G) : G := q * p * q⁻¹ * p⁻¹

/-- Projective-plane relator word: `r²`. -/
def rpWord (r : G) : G := r * r

/-- Gapped Klein-bottle braid constraint. -/
def KleinGappedConstraint (q p : G) : Prop := kleinWord q p = 1

/-- Gapped projective-plane braid constraint. -/
def RPGappedConstraint (r : G) : Prop := rpWord r = 1

/-- Gapless total EP charge on a Klein bottle has the relator-word form. -/
def KleinTotalEPCharge (q p : G) : G := kleinWord q p

/-- Gapless total EP charge on `RP²` has the relator-word form. -/
def RPTotalEPCharge (r : G) : G := rpWord r

/-! ## Abelianization consequences -/

/-- Additive Klein abelianization word. -/
def kleinAbelianWord (Aq Ap : ℤ) : ℤ := Aq + Ap - Aq + Ap

/-- Additive projective-plane abelianization word. -/
def rpAbelianWord (Ar : ℤ) : ℤ := Ar + Ar

/-- Klein abelianization reduces to `2 Ap`. -/
theorem kleinAbelianWord_eq (Aq Ap : ℤ) : kleinAbelianWord Aq Ap = 2 * Ap := by
  unfold kleinAbelianWord
  ring

/-- Projective-plane abelianization reduces to `2 Ar`. -/
theorem rpAbelianWord_eq (Ar : ℤ) : rpAbelianWord Ar = 2 * Ar := by
  unfold rpAbelianWord
  ring

/-- Abelianized Klein gapped constraint gives `2 Ap=0`. -/
theorem klein_abelian_torsion {Aq Ap : ℤ}
    (h : kleinAbelianWord Aq Ap = 0) : 2 * Ap = 0 := by
  simpa [kleinAbelianWord_eq] using h

/-- Abelianized `RP²` gapped constraint gives `2 Ar=0`. -/
theorem rp_abelian_torsion {Ar : ℤ}
    (h : rpAbelianWord Ar = 0) : 2 * Ar = 0 := by
  simpa [rpAbelianWord_eq] using h

/-- Torsion-free consequence in the two-band case `B₂ ≅ ℤ`: `2a=0 → a=0`. -/
theorem twoBand_torsionfree {a : ℤ} (h : 2 * a = 0) : a = 0 := by
  have h2 : (2 : ℤ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left h2

/-- In `B₂≅ℤ`, the Klein gapped invariant along the nonorientable direction vanishes. -/
theorem twoBand_klein_gapped_vanishes {Aq Ap : ℤ}
    (h : kleinAbelianWord Aq Ap = 0) : Ap = 0 :=
  twoBand_torsionfree (klein_abelian_torsion h)

/-- In `B₂≅ℤ`, the `RP²` gapped invariant vanishes. -/
theorem twoBand_rp_gapped_vanishes {Ar : ℤ}
    (h : rpAbelianWord Ar = 0) : Ar = 0 :=
  twoBand_torsionfree (rp_abelian_torsion h)

#check kleinAbelianWord_eq
#check rpAbelianWord_eq
#check twoBand_klein_gapped_vanishes
#check twoBand_rp_gapped_vanishes

end ExceptionalNonorientableTopology
