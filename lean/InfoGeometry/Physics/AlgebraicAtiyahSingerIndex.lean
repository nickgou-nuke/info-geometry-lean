import InfoGeometry.Physics.TQFTCobordismKasparovIndex
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

/-!
Algebraic index shadow for an idempotent twist.

This owner records the supertrace pairing of an even idempotent.  It is not
an analytic Fredholm index and does not claim the Atiyah--Singer theorem:
those statements require analytic and topological bridges not present here.
-/

set_option autoImplicit false

variable {A : Type*} [Ring A] [Algebra ℝ A]

structure AlgebraicIndexData (A : Type*) [Ring A] [Algebra ℝ A] where
  Tr : A →ₗ[ℝ] ℝ
  Gamma : A

abbrev KTheoryVectorBundle
    (A : Type*) [Ring A] [Algebra ℝ A]
    (data : AlgebraicIndexData A) :=
  {E : A // IsIdempotentElem E ∧ data.Gamma * E = E * data.Gamma}

namespace KTheoryVectorBundle

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {data : AlgebraicIndexData A}

abbrev E (bundle : KTheoryVectorBundle A data) : A := bundle.1

abbrev E_sq (bundle : KTheoryVectorBundle A data) : bundle.E * bundle.E = bundle.E :=
  bundle.2.1

abbrev E_even (bundle : KTheoryVectorBundle A data) :
    data.Gamma * bundle.E = bundle.E * data.Gamma :=
  bundle.2.2

end KTheoryVectorBundle

def analyticTwistedIndex
    (data : AlgebraicIndexData A)
    (bundle : KTheoryVectorBundle A data) : ℝ :=
  superTrace data.Tr data.Gamma bundle.E

def topologicalChernIndex
    (data : AlgebraicIndexData A)
    (bundle : KTheoryVectorBundle A data) : ℝ :=
  data.Tr (data.Gamma * bundle.E)

theorem algebraic_index_pairing_identity
    (data : AlgebraicIndexData A)
    (bundle : KTheoryVectorBundle A data) :
    analyticTwistedIndex data bundle = topologicalChernIndex data bundle := by
  simp only [analyticTwistedIndex, topologicalChernIndex, superTrace]

theorem chern_character_idempotent_trace
    (data : AlgebraicIndexData A)
    (bundle : KTheoryVectorBundle A data) :
    superTrace data.Tr data.Gamma bundle.E =
    superTrace data.Tr data.Gamma (bundle.E * bundle.E) := by
  change data.Tr (data.Gamma * bundle.E) =
    data.Tr (data.Gamma * (bundle.E * bundle.E))
  rw [bundle.E_sq]

end InfoGeometry.Physics
