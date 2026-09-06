import InfoGeometry.Physics.ChiralSUSYBlockFactorization
import InfoGeometry.Physics.SuperPoincareOperatorCharges
import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Physics.SupergradedCuntzBdG
import InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet
import InfoGeometry.OperatorAlgebra.SplitOctonionChiralFockSpectrum

/-!
# Split-Cayley/Cuntz/SUSY bridge

This file is an integration layer.  The chiral block factorisation, Cuntz
quotient, CAR/Fock spectrum, and polarized Cayley product remain owned by
their respective modules; this file only transports the already proved
relations to a common Cuntz-valued Weyl factor.

In particular, the finite results here do not assert a physical BdG model,
an Andreev scattering matrix, or a central extension.  A central charge still
requires an explicit commutation witness, as in
`SuperPoincareOperatorCharges`.
-/

noncomputable section

namespace InfoGeometry.Physics.SplitOctonionCuntzSUSYBridge

open Matrix
open InfoGeometry.Algebra.CuntzTensorQuotient

/-! ## Cuntz-valued Weyl factors -/

/-- A finite Cuntz-shift Weyl factor with coefficient profile `c`. -/
def cuntzWeylFactor (n : ℕ) (c : Fin n → ℂ) : CuntzAlg n :=
  ∑ i, (c i) • cuntzS n i

/-- The formal Cuntz adjoint of the weighted Weyl factor. -/
def cuntzWeylFactorSharp (n : ℕ) (c : Fin n → ℂ) : CuntzAlg n :=
  star (cuntzWeylFactor n c)

/-- Positive-chirality nilpotent block carrying the Cuntz Weyl factor. -/
def cuntzWeylQPlus (n : ℕ) (c : Fin n → ℂ) : ChiralBlock (CuntzAlg n) :=
  chiralQPlus (cuntzWeylFactor n c)

/-- Negative-chirality nilpotent block carrying the formal adjoint factor. -/
def cuntzWeylQMinus (n : ℕ) (c : Fin n → ℂ) : ChiralBlock (CuntzAlg n) :=
  chiralQMinus (cuntzWeylFactorSharp n c)

/-- The Dirac-type block assembled from the two Cuntz Weyl channels. -/
def cuntzWeylDirac (n : ℕ) (c : Fin n → ℂ) : ChiralBlock (CuntzAlg n) :=
  cuntzWeylQPlus n c + cuntzWeylQMinus n c

/-- The supersymmetric partner Hamiltonian block. -/
def cuntzWeylHamiltonian (n : ℕ) (c : Fin n → ℂ) : ChiralBlock (CuntzAlg n) :=
  chiralSUSYHamiltonian
    (cuntzWeylFactor n c) (cuntzWeylFactorSharp n c)

theorem cuntzWeylQPlus_sq (n : ℕ) (c : Fin n → ℂ) :
    cuntzWeylQPlus n c * cuntzWeylQPlus n c = 0 := by
  exact chiralQPlus_sq (cuntzWeylFactor n c)

theorem cuntzWeylQMinus_sq (n : ℕ) (c : Fin n → ℂ) :
    cuntzWeylQMinus n c * cuntzWeylQMinus n c = 0 := by
  exact chiralQMinus_sq (cuntzWeylFactorSharp n c)

theorem cuntzWeylDirac_sq (n : ℕ) (c : Fin n → ℂ) :
    cuntzWeylDirac n c * cuntzWeylDirac n c = cuntzWeylHamiltonian n c := by
  exact chiralDirac_sq_eq_susyHamiltonian
    (cuntzWeylFactor n c) (cuntzWeylFactorSharp n c)

theorem cuntzWeylParity_anticomm (n : ℕ) (c : Fin n → ℂ) :
    chiralParity * cuntzWeylDirac n c +
        cuntzWeylDirac n c * chiralParity = 0 := by
  unfold cuntzWeylDirac
  calc
    chiralParity * (cuntzWeylQPlus n c + cuntzWeylQMinus n c) +
        (cuntzWeylQPlus n c + cuntzWeylQMinus n c) * chiralParity =
        (chiralParity * cuntzWeylQPlus n c + cuntzWeylQPlus n c * chiralParity) +
          (chiralParity * cuntzWeylQMinus n c + cuntzWeylQMinus n c * chiralParity) := by
            noncomm_ring
    _ = 0 := by
      rw [show cuntzWeylQPlus n c = chiralQPlus (cuntzWeylFactor n c) from rfl,
        show cuntzWeylQMinus n c =
          chiralQMinus (cuntzWeylFactorSharp n c) from rfl,
        chiralParity_qPlus_anticomm, chiralParity_qMinus_anticomm]
      simp

/-! ## Central-charge boundary -/

/-- The unit Cuntz carrier is central, using the existing quotient theorem. -/
theorem cuntzUnit_central (n : ℕ) :
    ∀ X : CuntzAlg n, (1 : CuntzAlg n) * X = X * 1 := by
  intro X
  simp

/-- A Cayley triplet channel is structural data, not a central charge by name.
Centrality may only be concluded after a separate commutation hypothesis. -/
theorem central_charge_requires_commutation
    {A : Type*} [Ring A] {Z : A}
    (hZ : ∀ X : A, Z * X = X * Z) (X : A) :
    SuperPoincareOperatorCharges.comm Z X = 0 := by
  exact SuperPoincareOperatorCharges.comm_eq_zero_of_commutes (hZ X)

end InfoGeometry.Physics.SplitOctonionCuntzSUSYBridge
