import InfoGeometry.Automorphic.RoelckeSelbergSpectral
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Zeta Functions of Twisted Modular Curves

Formalizes the structural representation of the twisted modular curve L-function
from "ZETA FUNCTIONS OF TWISTED MODULAR CURVES" by Cristian Virdol (2006).
-/

noncomputable section

namespace InfoGeometry.Arithmetic.TwistedModularCurve

open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Automorphic.RoelckeSelbergSpectral

universe uBulk uBoundary uHecke uCohomology

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable {W : SiegelEisensteinWitness Bulk Boundary}
variable {HeckeIndex : Type uHecke}

/--
A weight-two cohomological cuspidal representation packet.

The carrier contains the actual mathematical witnesses:

* a joint Laplace-Hecke eigenvalue whose supplied weight is exactly two;
* a nonzero vector in the corresponding cuspidal joint eigenspace;
* a term in the model's cohomology-class type.

There are no unconstrained cohomological or fixed-vector proposition fields.
-/
abbrev AutomorphicRepresentation
    (R : RoelckeSelbergSpectralDatum W HeckeIndex)
    (weight : JointEigenvalue HeckeIndex → ℕ)
    (CohomologyClass : JointEigenvalue HeckeIndex → Type uCohomology) :=
  Σ chi : {chi : JointEigenvalue HeckeIndex // weight chi = 2},
    CuspidalEigenpacket R chi.1 × CohomologyClass chi.1

namespace AutomorphicRepresentation

variable {R : RoelckeSelbergSpectralDatum W HeckeIndex}
variable {weight : JointEigenvalue HeckeIndex → ℕ}
variable {CohomologyClass : JointEigenvalue HeckeIndex → Type uCohomology}

/-- The joint spectral character carried by a representation packet. -/
def eigenvalue
    (π : AutomorphicRepresentation R weight CohomologyClass) :
    JointEigenvalue HeckeIndex :=
  π.1.1

/-- The packet's concrete nonzero cuspidal joint eigenvector. -/
def eigenpacket
    (π : AutomorphicRepresentation R weight CohomologyClass) :
    CuspidalEigenpacket R π.eigenvalue :=
  π.2.1

/-- The packet's concrete cohomology class. -/
def cohomologyClass
    (π : AutomorphicRepresentation R weight CohomologyClass) :
    CohomologyClass π.eigenvalue :=
  π.2.2

/-- Every packet has weight two by construction. -/
theorem weight_eq_two
    (π : AutomorphicRepresentation R weight CohomologyClass) :
    weight π.eigenvalue = 2 :=
  π.1.2

/-- Every packet carries an actual nonzero vector in its joint cuspidal eigenspace. -/
theorem exists_nonzero_mem_jointEigenspace
    (π : AutomorphicRepresentation R weight CohomologyClass) :
    ∃ v : Bulk, v ≠ 0 ∧ v ∈ jointEigenspace R π.eigenvalue :=
  ⟨π.eigenpacket.vector, π.eigenpacket.nonzero, π.eigenpacket.mem_joint⟩

end AutomorphicRepresentation

/-- 
Proposition: The twisted modular curve L-function expansion (Theorem 1.1).
L(s, X'(p)) = \prod_{\pi} L(s, \rho_{\pi, \ell} \otimes (\tilde{\phi}_\pi \circ \rho))

The index type already consists of weight-two cohomological cuspidal
eigenpackets.  The individual factors are supplied by the repository's native
automorphic L-function datum.
-/
def twisted_modular_zeta_expansion_prop
    {R : RoelckeSelbergSpectralDatum W HeckeIndex}
    {weight : JointEigenvalue HeckeIndex → ℕ}
    {CohomologyClass : JointEigenvalue HeckeIndex → Type uCohomology}
    (L_curve : ℂ → ℂ)
    (L_auto : AutomorphicLFunctionDatum HeckeIndex)
    (valid_reps : Set (AutomorphicRepresentation R weight CohomologyClass)) : Prop :=
  ∀ s : ℂ,
    L_curve s =
      ∏' (π : valid_reps), L_auto.value π.val.eigenvalue s

end InfoGeometry.Arithmetic.TwistedModularCurve
