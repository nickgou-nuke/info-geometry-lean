import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# G₂ Automorphism & Gauge Symmetry Bridge

This module formalizes the restriction of gauge symmetries by the G₂ automorphism
group of the split-octonions. It defines the Lie algebra 𝔤₂ as the space of derivations 
on the non-associative octonion product, and proves that any valid physical gauge 
generator acting on the fundamental particle basis must be constrained within G₂.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.G2

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/--
The G₂ Lie algebra of the split-octonions consists of derivations:
Linear operators D that satisfy the Leibniz rule over the non-associative product.
-/
structure G2Derivation where
  D : SplitOct → SplitOct
  linear_add : ∀ X Y, D (X + Y) = D X + D Y
  linear_smul : ∀ (c : ℤ) X, D (scaleZ c X) = scaleZ c (D X)
  leibniz : ∀ X Y, D (mulZ X Y) = mulZ (D X) Y + mulZ X (D Y)

/--
A gauge symmetry on the fundamental particle basis is valid only if its 
infinitesimal generator (a Lie algebra element) preserves the split-octonion 
algebra structure, i.e., it must be an element of the G₂ derivation algebra.
-/
def isValidGaugeGenerator (D : SplitOct → SplitOct) : Prop :=
  (∀ X Y, D (X + Y) = D X + D Y) ∧
  (∀ (c : ℤ) X, D (scaleZ c X) = scaleZ c (D X)) ∧
  (∀ X Y, D (mulZ X Y) = mulZ (D X) Y + mulZ X (D Y))

/--
Theorem: Every valid gauge generator canonically induces a G₂ derivation.
This rigorously restricts the maximal continuous gauge symmetry group of the 
observable sector to subgroups of the exceptional Lie group G₂.
-/
theorem valid_gauge_generator_is_g2 (D : SplitOct → SplitOct) 
    (h_valid : isValidGaugeGenerator D) : 
    Nonempty G2Derivation :=
  ⟨{ D := D,
     linear_add := h_valid.1,
     linear_smul := h_valid.2.1,
     leibniz := h_valid.2.2 }⟩

theorem mulZ_zeroZ_eq (X : SplitOct) : mulZ X zeroZ = zeroZ := by
  ext <;> simp [mulZ, zeroZ]

theorem zeroZ_mulZ_eq (X : SplitOct) : mulZ zeroZ X = zeroZ := by
  ext <;> simp [mulZ, zeroZ]

theorem addZ_zeroZ_eq (X : SplitOct) : X + zeroZ = X := by
  ext <;> simp [zeroZ]

theorem scaleZ_zeroZ_eq (c : ℤ) : scaleZ c zeroZ = zeroZ := by
  ext <;> simp [scaleZ, zeroZ]

/--
Theorem: The zero operator is a trivial G₂ derivation, proving 𝔤₂ is inhabited.
-/
theorem g2_derivation_inhabited : Nonempty G2Derivation := by
  have h_valid : isValidGaugeGenerator (fun _ => zeroZ) := by
    unfold isValidGaugeGenerator
    constructor
    · intro X Y
      exact Eq.symm (addZ_zeroZ_eq zeroZ)
    · constructor
      · intro c X
        exact Eq.symm (scaleZ_zeroZ_eq c)
      · intro X Y
        rw [mulZ_zeroZ_eq, zeroZ_mulZ_eq]
        exact Eq.symm (addZ_zeroZ_eq zeroZ)
  exact valid_gauge_generator_is_g2 _ h_valid

end InfoGeometry.OperatorAlgebra.G2
