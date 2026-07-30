import InfoGeometry.OperatorAlgebra.SplitOctonionG2TypeGenerators

/-!
# Signed-permutation split-octonion automorphism witnesses

This module is the Lean twin of
`tools/sympy/split_octonion_signed_permutation_automorphisms.py`.

It adds the orientation-preserving signed transposition
`(x₀,x₁,x₂) ↦ (x₁,x₀,-x₂)` to the already-verified cyclic rotation `rho` and
signed flip `tau`.  The same signed permutation is applied to the upper and lower
Zorn vector slots, so dot and cross products are preserved in the explicit Zorn
multiplication.

Honesty boundary: this is another finite, concrete `G₂(2)`-type automorphism
surface.  It does not classify the full split-octonion automorphism group as
`G₂(2)` and does not derive an `SU(3)` stabilizer or particle theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.SignedPermutationAutomorphism

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism
open InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators

/-- Orientation-preserving signed transposition `(0 1)` plus a sign on coordinate `2`. -/
def sigma (X : SplitOct) : SplitOct :=
  ⟨X.a, X.b, X.x1, X.x0, -X.x2, X.y1, X.y0, -X.y2⟩

/-- `sigma` fixes the positive diagonal idempotent. -/
theorem sigma_ePlus : sigma ePlus = ePlus := by
  exact Eq.refl ePlus

/-- `sigma` fixes the negative diagonal idempotent. -/
theorem sigma_eMinus : sigma eMinus = eMinus := by
  exact Eq.refl eMinus

/-- `sigma` has order two. -/
theorem sigma_order_two (X : SplitOct) : sigma (sigma X) = X := by
  match X with
  | ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
      simp [sigma]

/-- `sigma` preserves the Zorn determinant / split norm. -/
theorem sigma_detZ (X : SplitOct) : detZ (sigma X) = detZ X := by
  cases X
  unfold sigma detZ
  ring

/-- `sigma` is multiplicative for the explicit Zorn product. -/
theorem sigma_mulZ (X Y : SplitOct) : sigma (mulZ X Y) = mulZ (sigma X) (sigma Y) := by
  cases X
  cases Y
  unfold sigma mulZ
  congr <;> ring

/-- `sigma` swaps `up0`, `up1` and negates `up2`. -/
theorem sigma_upper_slots :
    sigma up0 = up1 ∧ sigma up1 = up0 ∧ sigma up2 = negZ up2 := by
  exact ⟨Eq.refl up1, Eq.refl up0, Eq.refl (negZ up2)⟩

/-- `sigma` swaps `down0`, `down1` and negates `down2`. -/
theorem sigma_lower_slots :
    sigma down0 = down1 ∧ sigma down1 = down0 ∧ sigma down2 = negZ down2 := by
  exact ⟨Eq.refl down1, Eq.refl down0, Eq.refl (negZ down2)⟩

/-- Composite of the cyclic rotation with the signed transposition. -/
def rhoAfterSigma (X : SplitOct) : SplitOct := rho (sigma X)

/-- Composite of the signed transposition with the signed diagonal flip. -/
def sigmaAfterTau (X : SplitOct) : SplitOct := sigma (tau X)

/-- The composite `rho ∘ sigma` preserves multiplication. -/
theorem rhoAfterSigma_mulZ (X Y : SplitOct) :
    rhoAfterSigma (mulZ X Y) = mulZ (rhoAfterSigma X) (rhoAfterSigma Y) := by
  unfold rhoAfterSigma
  rw [sigma_mulZ, rho_mulZ]

/-- The composite `rho ∘ sigma` preserves the split norm. -/
theorem rhoAfterSigma_detZ (X : SplitOct) : detZ (rhoAfterSigma X) = detZ X := by
  unfold rhoAfterSigma
  rw [rho_detZ, sigma_detZ]

/-- The composite `sigma ∘ tau` preserves multiplication. -/
theorem sigmaAfterTau_mulZ (X Y : SplitOct) :
    sigmaAfterTau (mulZ X Y) = mulZ (sigmaAfterTau X) (sigmaAfterTau Y) := by
  unfold sigmaAfterTau
  rw [tau_mulZ, sigma_mulZ]

/-- The composite `sigma ∘ tau` preserves the split norm. -/
theorem sigmaAfterTau_detZ (X : SplitOct) : detZ (sigmaAfterTau X) = detZ X := by
  unfold sigmaAfterTau
  rw [sigma_detZ, tau_detZ]

end InfoGeometry.OperatorAlgebra.SplitOctonions.SignedPermutationAutomorphism
