import InfoGeometry.OperatorAlgebra.SplitOctonionCyclicAutomorphism

/-!
# Finite `G₂(2)`-type split-octonion automorphism generators

This module is the Lean twin of
`tools/sympy/split_octonion_signed_automorphisms.py`.

It adds a second concrete split-octonion automorphism to the cyclic coordinate
rotation from `SplitOctonionCyclicAutomorphism`: the orientation-preserving signed
coordinate flip `diag(1,-1,-1)` on both upper and lower Zorn vector slots.
Together with the cyclic rotation, this gives a finite generator surface inside
the split-octonion automorphism group.

Honesty boundary: this proves concrete `G₂(2)`-type automorphism witnesses.  It
does not classify the full automorphism group as `G₂(2)`, does not construct the
14-dimensional Lie algebra, and does not assert an `SU(3)` or particle theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism

/-- Orientation-preserving signed coordinate flip `diag(1,-1,-1)` on both vector slots. -/
def tau (X : SplitOct) : SplitOct :=
  ⟨X.a, X.b, X.x0, -X.x1, -X.x2, X.y0, -X.y1, -X.y2⟩

/-- `tau` fixes the positive diagonal idempotent. -/
theorem tau_ePlus : tau ePlus = ePlus := by
  exact Eq.refl ePlus

/-- `tau` fixes the negative diagonal idempotent. -/
theorem tau_eMinus : tau eMinus = eMinus := by
  exact Eq.refl eMinus

/-- The signed flip preserves the additive zero. -/
@[simp] theorem tau_zero : tau (0 : SplitOct) = 0 := by
  rfl

/-- The signed flip is additive on the explicit Zorn carrier. -/
theorem tau_add (X Y : SplitOct) : tau (X + Y) = tau X + tau Y := by
  cases X
  cases Y
  ext <;>
    simp [tau, add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2] <;>
    ring

/-- `tau` has order two. -/
theorem tau_order_two (X : SplitOct) : tau (tau X) = X := by
  match X with
  | ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
      simp [tau]

/-- `tau` preserves the Zorn determinant / split norm. -/
theorem tau_detZ (X : SplitOct) : detZ (tau X) = detZ X := by
  cases X
  unfold tau detZ
  ring

/-- `tau` is multiplicative for the explicit Zorn product. -/
theorem tau_mulZ (X Y : SplitOct) : tau (mulZ X Y) = mulZ (tau X) (tau Y) := by
  cases X
  cases Y
  unfold tau mulZ
  congr <;> ring

/-- `tau` fixes `up0` and changes signs on the other two upper slots. -/
theorem tau_upper_slots :
    tau up0 = up0 ∧ tau up1 = negZ up1 ∧ tau up2 = negZ up2 := by
  exact ⟨Eq.refl up0, Eq.refl (negZ up1), Eq.refl (negZ up2)⟩

/-- `tau` fixes `down0` and changes signs on the other two lower slots. -/
theorem tau_lower_slots :
    tau down0 = down0 ∧ tau down1 = negZ down1 ∧ tau down2 = negZ down2 := by
  exact ⟨Eq.refl down0, Eq.refl (negZ down1), Eq.refl (negZ down2)⟩

/-- Composite of the cyclic rotation with the signed flip. -/
def rhoAfterTau (X : SplitOct) : SplitOct := rho (tau X)

/-- The composite `rho ∘ tau` preserves multiplication. -/
theorem rhoAfterTau_mulZ (X Y : SplitOct) :
    rhoAfterTau (mulZ X Y) = mulZ (rhoAfterTau X) (rhoAfterTau Y) := by
  unfold rhoAfterTau
  rw [tau_mulZ, rho_mulZ]

/-- The composite `rho ∘ tau` preserves the split norm. -/
theorem rhoAfterTau_detZ (X : SplitOct) : detZ (rhoAfterTau X) = detZ X := by
  unfold rhoAfterTau
  rw [rho_detZ, tau_detZ]

end InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators
