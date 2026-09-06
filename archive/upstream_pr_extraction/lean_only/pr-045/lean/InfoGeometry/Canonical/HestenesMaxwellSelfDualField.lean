import InfoGeometry.Canonical.HestenesBivectorCarrier

namespace InfoGeometry.Canonical.HestenesMaxwell

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

/-- The Faraday Bivector represents the electromagnetic field F. -/
structure FaradayBivector (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q] where
  F : CliffordAlgebra Q
  is_bivector : F ∈ Bivector13 Q

/-- The 'Self-Dual' Electromagnetic Field: F_plus = F + F * Omega. -/
def selfDualField (F_biv : FaradayBivector Q) : CliffordAlgebra Q :=
  F_biv.F + F_biv.F * Omega (Q := Q)

/-- The 'Anti-Self-Dual' Electromagnetic Field: F_minus = F - F * Omega. -/
def antiSelfDualField (F_biv : FaradayBivector Q) : CliffordAlgebra Q :=
  F_biv.F - F_biv.F * Omega (Q := Q)

/-- In Minkowski spacetime, Hodge duality rotates F_plus into -F_minus. -/
theorem hodge_selfDualField (F_biv : FaradayBivector Q) :
    selfDualField Q F_biv * Omega (Q := Q) = - antiSelfDualField Q F_biv := by
  dsimp [selfDualField, antiSelfDualField]
  rw [add_mul, mul_assoc, omega_sq, mul_neg, mul_one]
  have h1 : -(F_biv.F - F_biv.F * Omega (Q := Q)) = F_biv.F * Omega (Q := Q) - F_biv.F := neg_sub F_biv.F (F_biv.F * Omega (Q := Q))
  rw [h1, sub_eq_add_neg]

/-- In Minkowski spacetime, Hodge duality rotates F_minus into F_plus. -/
theorem hodge_antiSelfDualField (F_biv : FaradayBivector Q) :
    antiSelfDualField Q F_biv * Omega (Q := Q) = selfDualField Q F_biv := by
  dsimp [selfDualField, antiSelfDualField]
  rw [sub_mul, mul_assoc, omega_sq, mul_neg, mul_one, sub_neg_eq_add, add_comm]

/-- Any Faraday bivector can be decomposed into Self-Dual and Anti-Self-Dual parts.
    F = 1/2 F_plus + 1/2 F_minus -/
theorem faraday_decomposition [Invertible (2 : R)] (F_biv : FaradayBivector Q) :
    F_biv.F = ⅟(2 : R) • selfDualField Q F_biv + ⅟(2 : R) • antiSelfDualField Q F_biv := by
  dsimp [selfDualField, antiSelfDualField]
  rw [smul_add, smul_sub]
  have h1 : ⅟(2 : R) • F_biv.F + ⅟(2 : R) • (F_biv.F * Omega (Q := Q)) + (⅟(2 : R) • F_biv.F - ⅟(2 : R) • (F_biv.F * Omega (Q := Q))) = ⅟(2 : R) • F_biv.F + ⅟(2 : R) • F_biv.F := by abel
  rw [h1, ←add_smul]
  have h2 : ⅟(2 : R) + ⅟(2 : R) = (1 : R) := by
    calc ⅟(2 : R) + ⅟(2 : R) = ⅟(2 : R) * (1 + 1) := by ring
      _ = ⅟(2 : R) * 2 := by ring
      _ = 1 := invOf_mul_self (2 : R)
  rw [h2, one_smul]

end InfoGeometry.Canonical.HestenesMaxwell
