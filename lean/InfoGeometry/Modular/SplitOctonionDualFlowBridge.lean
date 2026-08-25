import InfoGeometry.Lie.G2FromSplitOctonions

/-!
# Split-octonion dual-flow commutator bridge

This module separates the genuinely nonassociative split-octonion derivation
layer from the associative inner-derivation layer used for operator algebras.

For the explicit Zorn split-octonion product `mulZ`, define the bare product
commutator

`commZ K X = K * X - X * K`.

A split-octonion derivation `D` need not make `commZ K` itself a derivation.
Nevertheless the universal equivariance identity still holds pointwise:

`D (commZ K X) - commZ K (D X) = commZ (D K) X`.

The proof uses only additivity, compatibility with negation, and the Leibniz
rule.  No associativity assumption is used.
-/

noncomputable section

namespace InfoGeometry.Modular.SplitOctonionDualFlowBridge

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationData
open InfoGeometry.Lie.G2FromSplitOctonions

/-- Bare commutator for the true nonassociative Zorn split-octonion product. -/
def commZ (K X : SplitOct) : SplitOct :=
  subZ (mulZ K X) (mulZ X K)

/-- Subtraction is addition of the coordinatewise negative. -/
lemma subZ_eq_addZ_negZ (X Y : SplitOct) :
    subZ X Y = addZ X (negZ Y) := by
  ext <;> simp [subZ, addZ, negZ]

/-- Every bundled split-octonion derivation preserves coordinate subtraction. -/
lemma IsDeriv.map_subZ {D : DerivSpace} (hD : IsDeriv D) (X Y : SplitOct) :
    D (subZ X Y) = subZ (D X) (D Y) := by
  rcases hD with ⟨hadd, hneg, hmul⟩
  rw [subZ_eq_addZ_negZ, hadd, hneg, ← subZ_eq_addZ_negZ]

/--
The nonassociative dual-flow identity.

It is deliberately stated only as an identity of endomorphisms acting on an
element.  It does not assert that the bare commutator `commZ K` is itself a
split-octonion derivation.
-/
theorem derivation_commZ_comm {D : DerivSpace} (hD : IsDeriv D) (K X : SplitOct) :
    subZ (D (commZ K X)) (commZ K (D X)) = commZ (D K) X := by
  rw [commZ, hD.map_subZ]
  rw [hD.2.2 K X, hD.2.2 X K]
  ext <;> simp [commZ, subZ, addZ, mulZ] <;> ring

/-- If the generator is invariant under the geometric derivation, the two
pointwise flows commute. -/
theorem derivation_commZ_comm_of_invariant {D : DerivSpace} (hD : IsDeriv D)
    (K : SplitOct) (hK : D K = zeroZ) (X : SplitOct) :
    subZ (D (commZ K X)) (commZ K (D X)) = zeroZ := by
  rw [derivation_commZ_comm hD K X, hK]
  cases X
  simp [commZ, subZ, mulZ, zeroZ]

/-- Concrete specialization to the repository's native `rot01Derivation`. -/
theorem rot01_commZ_comm (K X : SplitOct) :
    subZ (rot01Derivation (commZ K X)) (commZ K (rot01Derivation X)) =
      commZ (rot01Derivation K) X :=
  derivation_commZ_comm D01_deriv K X

end InfoGeometry.Modular.SplitOctonionDualFlowBridge

end noncomputable section
