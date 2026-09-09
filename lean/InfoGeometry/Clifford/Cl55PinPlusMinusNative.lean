import InfoGeometry.Clifford.Clifford55

noncomputable section
namespace InfoGeometry.Clifford.Clifford55PinPlusMinusNative

open InfoGeometry.Clifford.Clifford55

/-!
The native Mathlib convention is used as follows:

* `PinPlus55` is the Pin subgroup for `Q55`;
* `PinMinus55` is the Pin subgroup for the opposite quadratic form `-Q55`.

For neutral signature `(5,5)` the two forms have the same signature, but they
are kept as different Clifford algebras.  This is the correct place to record
the two Pin conventions; identifying their algebras requires a separate
equivalence and is not definitionally valid.

The current Mathlib Clifford carrier is algebraic.  This file deliberately
does not install a fake discrete topology.  A genuine Lie/topological-group
completion needs a coordinate topology on the finite-dimensional Clifford
algebra and continuity proofs for its product and inverse.
-/

abbrev PinPlus55 := pinGroup Q55
abbrev Q55Opposite : QuadraticForm ℝ V55 := -Q55
abbrev Cl55Opposite := CliffordAlgebra Q55Opposite
abbrev PinMinus55 := pinGroup Q55Opposite

def swap55 : V55 →ₗ[ℝ] V55 where
  toFun v := (v.2, v.1)
  map_add' v w := by ext <;> rfl
  map_smul' c v := by ext <;> rfl

@[simp] theorem swap55_apply (v : V55) :
    swap55 v = (v.2, v.1) := by
  rfl

theorem Q55_swap_eq_neg (v : V55) :
    Q55 (swap55 v) = -Q55 v := by
  simp [swap55, Q55_apply]

theorem Q55Opposite_swap_eq (v : V55) :
    Q55Opposite (swap55 v) = Q55 v := by
  change -Q55 (swap55 v) = Q55 v
  rw [Q55_swap_eq_neg]
  ring

theorem Q55Opposite_apply (v : V55) :
    Q55Opposite v = -Q55 v := by
  rfl

/-! ## The sign-swapping quadratic and Clifford equivalences -/

noncomputable def swap55Equiv : V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofInvolutive swap55 (by
    intro v
    ext <;> rfl)

noncomputable def q55OppositeToQ55Isometry :
    Q55Opposite.IsometryEquiv Q55 :=
  { swap55Equiv with
    map_app' := by
      intro v
      change Q55 (swap55 v) = -Q55 v
      exact Q55_swap_eq_neg v }

noncomputable def cl55OppositeToQ55 :
    Cl55Opposite ≃ₐ[ℝ] CliffordAlgebra Q55 :=
  CliffordAlgebra.equivOfIsometry q55OppositeToQ55Isometry

@[simp] theorem cl55OppositeToQ55_ι (v : V55) :
    cl55OppositeToQ55 (CliffordAlgebra.ι Q55Opposite v) =
      CliffordAlgebra.ι Q55 (swap55 v) := by
  change CliffordAlgebra.map q55OppositeToQ55Isometry.toIsometry
      (CliffordAlgebra.ι Q55Opposite v) = _
  rw [CliffordAlgebra.map_apply_ι]
  congr 1

theorem pinPlus55_and_pinMinus55_are_native_subgroups :
    (PinPlus55 : Submonoid (CliffordAlgebra Q55)) = pinGroup Q55 ∧
      (PinMinus55 : Submonoid Cl55Opposite) = pinGroup Q55Opposite := by
  exact ⟨rfl, rfl⟩

end InfoGeometry.Clifford.Clifford55PinPlusMinusNative
