import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Physics.NuclearOperatorSchurComplement

/-!
# Klein-equivariant nuclear parameter Hamiltonians

This module connects the operator-valued Soloviev lane to the repository's
existing finite Klein orbit quotient.  The base carrier is the genuine finite
quotient from `D6HexTiledKleinBottleQuotient`; no new competing Klein model is
introduced here.

The Hamiltonian field is generally *equivariant*, not invariant, under one
base glide:

* diagonal coefficients are glide-invariant;
* off-diagonal channels change sign;
* internal parity conjugation realizes exactly the same sign reflection.

Consequently the Hamiltonian belongs naturally to a twisted/associated fibre
picture.  By contrast, the noncommutative Schur effective operator is genuinely
glide-invariant and therefore descends to an ordinary function on the finite
Klein quotient.

No global manifold homeomorphism, Pin structure, Berry phase, eigenvalue
monodromy, or physical cranking identification is asserted by this file.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearKleinParameterBundle

open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.Physics.NuclearOperatorSchurComplement

variable {A : Type*} [Ring A]

abbrev ParameterCell := TorusCell
abbrev KleinParameterQuotient := KleinHexQuotient

/-- An operator-valued Soloviev field on the finite torus cover, equipped with
pointwise internal parity and the exact Klein-glide transformation law. -/
structure KleinEquivariantHamiltonian (P : InternalParity A) where
  E0 : ParameterCell → A
  E1 : ParameterCell → A
  V : ParameterCell → A
  W : ParameterCell → A
  E0_even : ∀ p, P.IsEven (E0 p)
  E1_even : ∀ p, P.IsEven (E1 p)
  V_odd : ∀ p, P.IsOdd (V p)
  W_odd : ∀ p, P.IsOdd (W p)
  E0_glide : ∀ p, E0 (glide p) = E0 p
  E1_glide : ∀ p, E1 (glide p) = E1 p
  V_glide : ∀ p, V (glide p) = -V p
  W_glide : ∀ p, W (glide p) = -W p

namespace KleinEquivariantHamiltonian

variable {P : InternalParity A} (H : KleinEquivariantHamiltonian P)

/-- The full operator block at a cover point. -/
def blockAt (p : ParameterCell) : Block2 A :=
  blockHamiltonian (H.E0 p) (H.E1 p) (H.V p) (H.W p)

/-- One base glide is exactly off-diagonal Soloviev reflection. -/
theorem blockAt_glide (p : ParameterCell) :
    H.blockAt (glide p) =
      reflectOffDiagonal (H.E0 p) (H.E1 p) (H.V p) (H.W p) := by
  simp [blockAt, reflectOffDiagonal, blockHamiltonian,
    H.E0_glide p, H.E1_glide p, H.V_glide p, H.W_glide p]

/-- Internal parity holonomy realizes the base glide on the operator block. -/
theorem internalParity_holonomy (p : ParameterCell) :
    internalParity P * H.blockAt p * internalParity P =
      H.blockAt (glide p) := by
  rw [H.blockAt_glide]
  exact internalParity_reflection_of_even_diagonal_odd_offDiagonal
    P (H.E0 p) (H.E1 p) (H.V p) (H.W p)
      (H.E0_even p) (H.E1_even p) (H.V_odd p) (H.W_odd p)

/-- External Fock parity gives the same fibre reflection as one base glide. -/
theorem externalParity_holonomy (p : ParameterCell) :
    (externalFockParity : Block2 A) * H.blockAt p * externalFockParity =
      H.blockAt (glide p) := by
  rw [H.blockAt_glide]
  exact externalFockParity_reflection
    (H.E0 p) (H.E1 p) (H.V p) (H.W p)

/-- The square of the glide returns every coefficient to its original value.
The finite base glide itself need not be the identity after two steps. -/
theorem coefficients_glide2 (p : ParameterCell) :
    H.E0 (glide2 p) = H.E0 p ∧
      H.E1 (glide2 p) = H.E1 p ∧
      H.V (glide2 p) = H.V p ∧
      H.W (glide2 p) = H.W p := by
  constructor
  · change H.E0 (glide (glide p)) = H.E0 p
    rw [H.E0_glide, H.E0_glide]
  constructor
  · change H.E1 (glide (glide p)) = H.E1 p
    rw [H.E1_glide, H.E1_glide]
  constructor
  · rw [glide2, H.V_glide, H.V_glide, neg_neg]
  · rw [glide2, H.W_glide, H.W_glide, neg_neg]

/-- After two glides the operator block is unchanged, while the base point has
moved by the nontrivial horizontal translation encoded by `glide_square`. -/
theorem blockAt_glide2 (p : ParameterCell) :
    H.blockAt (glide2 p) = H.blockAt p := by
  rcases H.coefficients_glide2 p with ⟨h0, h1, hV, hW⟩
  simp [blockAt, h0, h1, hV, hW]

/-- Total parity is a genuine fibre symmetry at each parameter point. -/
theorem totalParity_fibre_invariant (p : ParameterCell) :
    totalParity P * H.blockAt p * totalParity P = H.blockAt p := by
  exact totalParity_invariance_from_double_reflection
    P (H.E0 p) (H.E1 p) (H.V p) (H.W p)
      (H.E0_even p) (H.E1_even p) (H.V_odd p) (H.W_odd p)

/-- Effective Schur operator associated with fixed proof-carrying resolvent data. -/
def effectiveAt (R : ResolventData A) (p : ParameterCell) : A :=
  effectiveOperator (H.E0 p) (H.V p) (H.W p) R.inv

/-- The Schur effective operator is invariant under the Klein glide. -/
theorem effectiveAt_glide (R : ResolventData A) (p : ParameterCell) :
    H.effectiveAt R (glide p) = H.effectiveAt R p := by
  unfold effectiveAt
  rw [H.E0_glide, H.V_glide, H.W_glide]
  exact effectiveOperator_reflection (H.E0 p) (H.V p) (H.W p) R.inv

/-- Glide invariance propagates to all four elements of the finite orbit. -/
theorem effectiveAt_orbit_invariant
    (R : ResolventData A) {p q : ParameterCell}
    (hpq : kleinOrbitRel p q) :
    H.effectiveAt R p = H.effectiveAt R q := by
  rcases hpq with rfl | rfl | rfl | rfl
  · rfl
  · exact (H.effectiveAt_glide R p).symm
  · rw [glide2]
    rw [H.effectiveAt_glide R (glide p), H.effectiveAt_glide R p]
  · rw [glide3]
    calc
      H.effectiveAt R p = H.effectiveAt R (glide p) :=
        (H.effectiveAt_glide R p).symm
      _ = H.effectiveAt R (glide2 p) := by
        change H.effectiveAt R (glide p) =
          H.effectiveAt R (glide (glide p))
        exact (H.effectiveAt_glide R (glide p)).symm
      _ = H.effectiveAt R (glide3 p) :=
        (H.effectiveAt_glide R (glide2 p)).symm

/-- The glide-invariant effective operator descends to the genuine finite Klein quotient. -/
def quotientEffectiveOperator (R : ResolventData A) :
    KleinParameterQuotient → A :=
  Quotient.lift (H.effectiveAt R)
    (fun p q hpq => H.effectiveAt_orbit_invariant R hpq)

@[simp] theorem quotientEffectiveOperator_mk
    (R : ResolventData A) (p : ParameterCell) :
    H.quotientEffectiveOperator R (quotientMap p) = H.effectiveAt R p := rfl

/-- Consolidated Klein-equivariant nuclear packet. -/
theorem klein_parameter_packet
    (R : ResolventData A) (p : ParameterCell) :
    internalParity P * H.blockAt p * internalParity P = H.blockAt (glide p) ∧
      (externalFockParity : Block2 A) * H.blockAt p * externalFockParity =
        H.blockAt (glide p) ∧
      totalParity P * H.blockAt p * totalParity P = H.blockAt p ∧
      H.effectiveAt R (glide p) = H.effectiveAt R p :=
  ⟨H.internalParity_holonomy p,
    H.externalParity_holonomy p,
    H.totalParity_fibre_invariant p,
    H.effectiveAt_glide R p⟩

end KleinEquivariantHamiltonian

end InfoGeometry.Physics.NuclearKleinParameterBundle

end noncomputable section
