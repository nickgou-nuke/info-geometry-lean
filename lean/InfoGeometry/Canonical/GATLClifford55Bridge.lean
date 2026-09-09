import Mathlib.Tactic
import InfoGeometry.Clifford.Clifford55

/-!
# Native Mathlib presentation of the `Cl(5,5)` group carriers

This is the theorem-safe part of the GATL-style translation.  Mathlib's
`pinGroup` and `spinGroup` are submonoids of the Clifford algebra, while the
Lipschitz group is a subgroup of its unit group.  The final declaration is
only the span of quadratic Clifford products; it is not called a Lie algebra
because bracket closure has not been proved here.
-/

noncomputable section

namespace InfoGeometry.Canonical.GATLClifford55Bridge

open InfoGeometry.Clifford.Clifford55

abbrev CliffordGroup : Subgroup Cl55ˣ := LipschitzGroup55

abbrev PinGroup_GATL : Submonoid Cl55 := pinGroup Q55

@[simp] theorem pin_gatl_eq_pin55 : PinGroup_GATL = Pin55 := rfl

abbrev SpinGroup_GATL : Submonoid Cl55 := spinGroup Q55

@[simp] theorem spin_gatl_eq_spin55 : SpinGroup_GATL = Spin55 := rfl

theorem pin_coe_mem_pin55 (g : PinGroup_GATL) :
    (g : Cl55) ∈ Pin55 := by
  exact g.2

theorem spin_coe_mem_spin55 (g : SpinGroup_GATL) :
    (g : Cl55) ∈ Spin55 := by
  exact g.2

theorem pin_units_mem_lipschitz (g : PinGroup_GATL) :
    pinToUnits g ∈ LipschitzGroup55 := by
  exact InfoGeometry.Clifford.Clifford55.pin_units_mem_lipschitz g

def quadraticCliffordGenerator (v w : V55) : Cl55 :=
  ι55 v * ι55 w

def CliffordBivectorSpan55 : Submodule ℝ Cl55 :=
  Submodule.span ℝ (Set.range fun p : V55 × V55 =>
    quadraticCliffordGenerator p.1 p.2)

theorem quadraticCliffordGenerator_mem_span (v w : V55) :
    quadraticCliffordGenerator v w ∈ CliffordBivectorSpan55 := by
  exact Submodule.subset_span (Set.mem_range_self (v, w))

theorem quadraticCliffordGenerator_add_left (v₁ v₂ w : V55) :
    quadraticCliffordGenerator (v₁ + v₂) w =
      quadraticCliffordGenerator v₁ w + quadraticCliffordGenerator v₂ w := by
  simp [quadraticCliffordGenerator, add_mul]

theorem quadraticCliffordGenerator_add_right (v w₁ w₂ : V55) :
    quadraticCliffordGenerator v (w₁ + w₂) =
      quadraticCliffordGenerator v w₁ + quadraticCliffordGenerator v w₂ := by
  simp [quadraticCliffordGenerator, mul_add]

theorem quadraticCliffordGenerator_smul_left (a : ℝ) (v w : V55) :
    quadraticCliffordGenerator (a • v) w =
      a • quadraticCliffordGenerator v w := by
  simp [quadraticCliffordGenerator]

theorem quadraticCliffordGenerator_smul_right (a : ℝ) (v w : V55) :
    quadraticCliffordGenerator v (a • w) =
      a • quadraticCliffordGenerator v w := by
  simp [quadraticCliffordGenerator]

end InfoGeometry.Canonical.GATLClifford55Bridge
