import InfoGeometry.Canonical.BerryConnection

/-!
# Supergraded Jordan–Lie Split on the Doubled Krein Carrier

This file records the operatorial Jordan/Lie split of the Clifford product on
`DoubledSpace E`, aligned with the supergraded commutator/anticommutator
channels carried by `SuperHestenesKaehlerDatum`.
-/

namespace InfoGeometry.Canonical.SuperJordanLie

open InfoGeometry.Canonical.BerryPhase
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Jordan product (symmetric) on doubled-space endomorphisms. -/
noncomputable def jordanProduct (A B : EndH) : EndH :=
  (1 / 2 : ℝ) • (A.comp B + B.comp A)

/-- Lie product (antisymmetric) on doubled-space endomorphisms. -/
noncomputable def lieProduct (A B : EndH) : EndH :=
  (1 / 2 : ℝ) • (A.comp B - B.comp A)

theorem fockCommutator_eq_two_smul_lieProduct
    (A B : EndH) :
    fockCommutator (E := E) A B = (2 : ℝ) • lieProduct A B := by
  simp [fockCommutator,
    InfoGeometry.Canonical.BogoliubovFockSuper.superBracket_even_left,
    lieProduct, sub_eq_add_neg, smul_smul]

theorem fockAnticommutator_eq_two_smul_jordanProduct
    (A B : EndH) :
    fockAnticommutator (E := E) A B = (2 : ℝ) • jordanProduct A B := by
  simp [fockAnticommutator,
    InfoGeometry.Canonical.BogoliubovFockSuper.superBracket_odd_odd,
    jordanProduct, smul_smul]

end InfoGeometry.Canonical.SuperJordanLie
