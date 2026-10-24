/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.TracialCARDensity

/-! # Weighted commutator and density–Majorana identities

Uncompiled G-A sandbox extension. The Majorana combinations are written
explicitly as ann+cre and ann-cre; no new operator or bracket is defined.
All identities are division-free, including in characteristic two.
-/
namespace InfoGeometry.OperatorAlgebra.TracialCARDensity

open InfoGeometry.NCG
open InfoGeometry.OperatorAlgebra.CARProjectors
open SplitClifford

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The weighted commutator is measured by the density's commutator with x. -/
theorem weighted_commutator_defect (τ : TracialFunctional R A) (ρ x y : A) :
    weighted τ ρ (x * y - y * x) = τ ((ρ * x - x * ρ) * y) := by
  have h : τ (ρ * (y * x)) = τ ((x * ρ) * y) := by
    calc
      _ = τ ((ρ * y) * x) := by rw [mul_assoc]
      _ = τ (x * (ρ * y)) := τ.cyclic _ _
      _ = _ := by rw [mul_assoc]
  change τ (ρ * (x * y - y * x)) = _
  rw [mul_sub, τ.map_sub, sub_mul, τ.map_sub, h, mul_assoc ρ x y]

/-- Density commutator with the sum Majorana combination. -/
theorem density_commutator_majorana_plus (P : CARPair A) (a c : R) :
    density P a c * (P.ann + P.cre) - (P.ann + P.cre) * density P a c =
      (c - a) • (P.ann - P.cre) := by
  simp only [mul_add, add_mul, density_mul_ann, density_mul_cre,
    ann_mul_density, cre_mul_density]
  module

/-- Density commutator with the difference Majorana combination. -/
theorem density_commutator_majorana_minus (P : CARPair A) (a c : R) :
    density P a c * (P.ann - P.cre) - (P.ann - P.cre) * density P a c =
      (c - a) • (P.ann + P.cre) := by
  simp only [mul_sub, sub_mul, density_mul_ann, density_mul_cre,
    ann_mul_density, cre_mul_density]
  module

/-- Density anticommutator with the sum Majorana combination. -/
theorem density_anticommutator_majorana_plus (P : CARPair A) (a c : R) :
    density P a c * (P.ann + P.cre) + (P.ann + P.cre) * density P a c =
      (a + c) • (P.ann + P.cre) := by
  simp only [mul_add, add_mul, density_mul_ann, density_mul_cre,
    ann_mul_density, cre_mul_density]
  module

/-- Density anticommutator with the difference Majorana combination. -/
theorem density_anticommutator_majorana_minus (P : CARPair A) (a c : R) :
    density P a c * (P.ann - P.cre) + (P.ann - P.cre) * density P a c =
      (a + c) • (P.ann - P.cre) := by
  simp only [mul_sub, sub_mul, density_mul_ann, density_mul_cre,
    ann_mul_density, cre_mul_density]
  module

/-- Native chirality is vacuum minus occupation. This decomposition does not
invert two or assert recovery from reflection eigenspaces in characteristic two. -/
theorem two_smul_density (P : CARPair A) (a c : R) :
    (2 : R) • density P a c =
      (a + c) • (1 : A) + (c - a) • chirality P := by
  rw [← projectors_add P]
  simp only [density, chirality]
  module

/-- Division-free annihilator boundary equation in commutator form. -/
theorem annihilator_commutator_boundary (τ : TracialFunctional R A)
    (P : CARPair A) (a c : R) (x : A) :
    a * weighted τ (density P a c) (P.ann * x - x * P.ann) =
      (c - a) * weighted τ (density P a c) (x * P.ann) := by
  rw [map_sub, mul_sub, annihilatorKMS τ P a c x]
  ring

end InfoGeometry.OperatorAlgebra.TracialCARDensity
