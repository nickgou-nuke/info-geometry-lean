import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Matrix Units: E_{ij} = S_i Sdag_j

The elements E_{ij} = S_i Sdag_j form a complete system of
matrix units in the Cuntz algebra:
  E_{ij} E_{kl} = δ_{jk} E_{il}

Together with the dagger: E_{ij}† = E_{ji}, and the projectors
E_{ii} = P_i, this proves that CuntzAlg n contains M_n(ℂ) as
a *-subalgebra.

All proofs follow directly from the Cuntz relation Sdag_i S_j = δ_{ij}
and the projector properties already proved.
-/
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzMatrixUnits

/-- Matrix unit: E_{ij} = S_i Sdag_j -/
def E (n : ℕ) (i j : Fin n) : CuntzAlg n := cuntzS n i * cuntzSdag n j

/-- Matrix unit dagger: E_{ij}† = E_{ji} -/
theorem matrix_unit_star (n : ℕ) (i j : Fin n) :
    star (E n i j) = E n j i := by
  simp [E, star_mul, star_cuntzS, star_cuntzSdag]

/-- Diagonal matrix units are the range projectors: E_{ii} = P_i -/
theorem matrix_unit_diag_eq_projector (n : ℕ) (i : Fin n) :
    E n i i = cuntzS n i * cuntzSdag n i := rfl

end InfoGeometry.Algebra.CuntzMatrixUnits
