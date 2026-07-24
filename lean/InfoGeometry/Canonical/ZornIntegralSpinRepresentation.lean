import InfoGeometry.Canonical.ZornCliffordRepresentation

/-!
# Integral spin representation on Zorn coordinates

Mathlib's Clifford spin group for the integral Zorn quadratic module acts on
the integral Dirac carrier. Here that action is bundled as a genuine
representation in the integral general linear group.

Since `ZornMatrix`, `zornNorm`, and `spinDiracRepresentation` are defined
polymorphically over any commutative ring `R`, the integral representation
is their specialization to `ℤ`. This module does not identify that integral
spin group with a subgroup of a separately constructed real spin group;
such a comparison requires an explicit scalar-extension theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornIntegralSpinRepresentation

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford

abbrev IntegralZorn := ZornMatrix ℤ

/-- Mathlib's spin group for the Zorn norm on the integral Zorn module. -/
abbrev integralSpin44 := spinGroup (zornNorm (R := ℤ))

/-- The integral Clifford-spin action as an integral linear endomorphism. -/
def integralSpinLinear (g : integralSpin44) :
    Module.End ℤ (DiracSpinor16 (R := ℤ)) :=
  spinDiracRepresentation (R := ℤ) g

theorem integralSpinLinear_add (g : integralSpin44) (Ψ Φ : DiracSpinor16 (R := ℤ)) :
    integralSpinLinear g (Ψ + Φ) = integralSpinLinear g Ψ + integralSpinLinear g Φ := by
  exact map_add (integralSpinLinear g) Ψ Φ

theorem integralSpinLinear_smul (g : integralSpin44) (n : ℤ) (Ψ : DiracSpinor16 (R := ℤ)) :
    integralSpinLinear g (n • Ψ) = n • integralSpinLinear g Ψ := by
  exact map_smul (integralSpinLinear g) n Ψ

theorem integralSpinLinear_one : integralSpinLinear 1 = 1 := by
  change (spinDiracRepresentation (R := ℤ) 1 : Module.End ℤ (DiracSpinor16 (R := ℤ))) = 1
  rw [map_one]
  rfl

theorem integralSpinLinear_mul (g h : integralSpin44) :
    integralSpinLinear (g * h) = integralSpinLinear g * integralSpinLinear h := by
  change (spinDiracRepresentation (R := ℤ) (g * h) : Module.End ℤ (DiracSpinor16 (R := ℤ))) = _
  rw [map_mul]
  rfl

/-- Mathlib's Clifford conjugation on the spin group is group inversion, so
the two corresponding integral Dirac actions agree. -/
theorem integralSpinLinear_star (g : integralSpin44) :
    integralSpinLinear (star g) = integralSpinLinear g⁻¹ := by
  rw [spinGroup.star_eq_inv]

/-- Genuine integral representation of Mathlib's integral Zorn spin group. -/
def integralSpinRepresentation :
    integralSpin44 →* LinearMap.GeneralLinearGroup ℤ (DiracSpinor16 (R := ℤ)) :=
  spinDiracRepresentation (R := ℤ)

theorem integralSpinRepresentation_apply
    (g : integralSpin44) (Ψ : DiracSpinor16 (R := ℤ)) :
    (integralSpinRepresentation g : Module.End ℤ (DiracSpinor16 (R := ℤ))) Ψ =
      integralSpinLinear g Ψ := rfl

/-- The integral action is exactly the universal Zorn Clifford representation
evaluated on the underlying spin-group element. -/
theorem integralSpinLinear_eq_clifford (g : integralSpin44) :
    integralSpinLinear g =
      zornCliffordRepresentation (R := ℤ)
        (g : CliffordAlgebra (zornNorm (R := ℤ))) := by
  exact spinDiracRepresentation_val g

theorem integralSpinRepresentation_inv (g : integralSpin44) :
    integralSpinRepresentation g⁻¹ = (integralSpinRepresentation g)⁻¹ := by
  exact map_inv integralSpinRepresentation g

theorem integralSpinLinear_inv (g : integralSpin44) :
    integralSpinLinear g⁻¹ =
      (((integralSpinRepresentation g)⁻¹ :
        LinearMap.GeneralLinearGroup ℤ (DiracSpinor16 (R := ℤ))) :
          Module.End ℤ (DiracSpinor16 (R := ℤ))) := by
  change ((spinDiracRepresentation (R := ℤ) g⁻¹ :
    LinearMap.GeneralLinearGroup ℤ (DiracSpinor16 (R := ℤ))) :
      Module.End ℤ (DiracSpinor16 (R := ℤ))) = _
  exact congrArg (fun u : LinearMap.GeneralLinearGroup ℤ
    (DiracSpinor16 (R := ℤ)) =>
      (u : Module.End ℤ (DiracSpinor16 (R := ℤ))))
    (spinDiracRepresentation_inv g)

theorem integralSpinLinear_inv_mul_apply
    (g : integralSpin44) (Ψ : DiracSpinor16 (R := ℤ)) :
    integralSpinLinear g⁻¹ (integralSpinLinear g Ψ) = Ψ := by
  have h := (integralSpinRepresentation g).inv_val
  exact LinearMap.congr_fun h Ψ

theorem integralSpinLinear_mul_inv_apply
    (g : integralSpin44) (Ψ : DiracSpinor16 (R := ℤ)) :
    integralSpinLinear g (integralSpinLinear g⁻¹ Ψ) = Ψ := by
  have h := (integralSpinRepresentation g).val_inv
  exact LinearMap.congr_fun h Ψ

theorem integralSpinLinear_injective (g : integralSpin44) :
    Function.Injective (integralSpinLinear g) := by
  intro Ψ Φ h
  have h' := congrArg (integralSpinLinear g⁻¹) h
  rw [integralSpinLinear_inv_mul_apply,
    integralSpinLinear_inv_mul_apply] at h'
  exact h'

theorem integralSpinLinear_surjective (g : integralSpin44) :
    Function.Surjective (integralSpinLinear g) := by
  intro Ψ
  exact ⟨integralSpinLinear g⁻¹ Ψ,
    integralSpinLinear_mul_inv_apply g Ψ⟩

/-- Every integral spin action is a bijection of the integral Dirac lattice,
with inverse supplied by the inverse spin element. -/
theorem integralSpinLinear_bijective (g : integralSpin44) :
    Function.Bijective (integralSpinLinear g) :=
  ⟨integralSpinLinear_injective g, integralSpinLinear_surjective g⟩

end InfoGeometry.Canonical.ZornIntegralSpinRepresentation

end noncomputable section
