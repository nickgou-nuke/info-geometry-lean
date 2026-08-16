import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Concrete cyclic split-octonion automorphism

This module is the Lean twin of
`tools/sympy/split_octonion_cyclic_automorphism.py`.

It proves one exact order-three automorphism of the explicit Zorn split-octonion
multiplication surface.  The map fixes the two diagonal idempotents and cyclically
permutes the three upper and lower vector slots by the same orientation-preserving
cycle:

```text
u₀ ↦ u₁ ↦ u₂ ↦ u₀,
v₀ ↦ v₁ ↦ v₂ ↦ v₀.
```

This is a concrete `G₂(2)`-type automorphism property for the split-octonion
multiplication table.  It is not a group-classification theorem saying that the
full automorphism group is `G₂(2)`, and it does not assert any `SU(3)` stabilizer
or particle-classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Orientation-preserving cyclic rotation of the three Zorn vector coordinates. -/
def rho (X : SplitOct) : SplitOct :=
  ⟨X.a, X.b, X.x2, X.x0, X.x1, X.y2, X.y0, X.y1⟩

/-- `rho` fixes the positive diagonal idempotent. -/
theorem rho_ePlus : rho ePlus = ePlus := by
  exact Eq.refl ePlus

/-- `rho` fixes the negative diagonal idempotent. -/
theorem rho_eMinus : rho eMinus = eMinus := by
  exact Eq.refl eMinus

/-- The cyclic map preserves the additive zero. -/
@[simp] theorem rho_zero : rho (0 : SplitOct) = 0 := by
  rfl

/-- The cyclic map is additive on the explicit Zorn carrier. -/
theorem rho_add (X Y : SplitOct) : rho (X + Y) = rho X + rho Y := by
  cases X
  cases Y
  rfl

/-- `rho` cyclically permutes the upper `1 + 3` vector slots. -/
theorem rho_upper_slots : rho up0 = up1 ∧ rho up1 = up2 ∧ rho up2 = up0 := by
  exact ⟨Eq.refl up1, Eq.refl up2, Eq.refl up0⟩

/-- `rho` cyclically permutes the lower `1 + 3` vector slots. -/
theorem rho_lower_slots : rho down0 = down1 ∧ rho down1 = down2 ∧ rho down2 = down0 := by
  exact ⟨Eq.refl down1, Eq.refl down2, Eq.refl down0⟩

/-- The cyclic map has order three. -/
theorem rho_order_three (X : SplitOct) : rho (rho (rho X)) = X := by
  match X with
  | ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
      exact Eq.refl (SplitOct.mk a b x0 x1 x2 y0 y1 y2)

/-- The cyclic map preserves the Zorn determinant / split norm. -/
theorem rho_detZ (X : SplitOct) : detZ (rho X) = detZ X := by
  cases X
  unfold rho detZ
  ring

/-- The cyclic map is multiplicative for the explicit Zorn product. -/
theorem rho_mulZ (X Y : SplitOct) : rho (mulZ X Y) = mulZ (rho X) (rho Y) := by
  cases X
  cases Y
  unfold rho mulZ
  congr <;> ring

/-- Applying `rho` transports the basic upper cyclic product table equivariantly. -/
theorem rho_transports_upper_cycle :
    rho (mulZ up0 up1) = mulZ (rho up0) (rho up1) ∧
      rho (mulZ up1 up2) = mulZ (rho up1) (rho up2) ∧
      rho (mulZ up2 up0) = mulZ (rho up2) (rho up0) := by
  exact ⟨rho_mulZ up0 up1, rho_mulZ up1 up2, rho_mulZ up2 up0⟩

/-- Applying `rho` transports the basic lower cyclic product table equivariantly. -/
theorem rho_transports_lower_cycle :
    rho (mulZ down0 down1) = mulZ (rho down0) (rho down1) ∧
      rho (mulZ down1 down2) = mulZ (rho down1) (rho down2) ∧
      rho (mulZ down2 down0) = mulZ (rho down2) (rho down0) := by
  exact ⟨rho_mulZ down0 down1, rho_mulZ down1 down2, rho_mulZ down2 down0⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism
